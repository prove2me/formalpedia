-- Prove2me | solution 1 for GlobalTheory.AdaptedCoord.fderiv_eq_zero_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:11.710021+00:00
-- url     : https://prove2.me/submissions/dd5a2dae-199a-4b0b-92e8-44293d5ec105

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Theorems.Thm_GlobalTheory_AdaptedCoord_eventually_le
import Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_apply
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
namespace AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
private theorem preimage_whole_of_closedPoint_mem' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ W ↔ x (default : PrimeSpectrum ℂ) ∈ W := by
  constructor
  · intro h
    exact h (show (default : PrimeSpectrum ℂ) ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h q _
    have hq : q = (default : PrimeSpectrum ℂ) := @Subsingleton.elim (PrimeSpectrum ℂ) _ q default
    subst hq
    exact h
end AdaptedCoord
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.AdaptedCoord
theorem _root_.solution {U : A.left.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (w : Fin g → ℂ) (hw : dirDeriv u h w = 0) (V : A.left.Opens) (f : Γ(A.left, V))
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) : fderiv ℂ (fun z => valAt' (u.ex z).left V f) 0 w = 0 := by
  classical

  have hxU := (preimage_whole_of_closedPoint_mem' (u.ex 0).left U).1 h
  have hxV := (preimage_whole_of_closedPoint_mem' (u.ex 0).left V).1 hV
  obtain ⟨b, hbV, hxb⟩ := hU.exists_basicOpen_le (V := V) ⟨_, hxV⟩ hxU
  have hb0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ A.left.basicOpen b := (preimage_whole_of_closedPoint_mem' _ _).2 hxb
  have hloc := hU.isLocalization_basicOpen b
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers b)
    (A.left.presheaf.map (homOfLE hbV).op f)
  dsimp only at hs
  have hres : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen b → ∀ c : Γ(A.left, U),
      valAt' (u.ex z).left (A.left.basicOpen b)
        (algebraMap Γ(A.left, U) Γ(A.left, A.left.basicOpen b) c) = valAt' (u.ex z).left U c :=
    fun z hz c => by
      exact valAt'_res _ (A.left.basicOpen_le b) c hz

  have hev : (fun z => valAt' (u.ex z).left V f * valAt' (u.ex z).left U (s : Γ(A.left, U))) =ᶠ[𝓝 0]
      fun z => valAt' (u.ex z).left U a := by
    filter_upwards [eventually_le u hb0] with z hz
    have hf : valAt' (u.ex z).left (A.left.basicOpen b) (A.left.presheaf.map (homOfLE hbV).op f) =
        valAt' (u.ex z).left V f := by
      exact valAt'_res _ hbV f hz
    rw [← hres z hz a, ← hres z hz (s : Γ(A.left, U)), ← hs, valAt'_mul, hf]
  have hDa : fderiv ℂ (fun z => valAt' (u.ex z).left U a) 0 w = 0 := by
    rw [← dirDeriv_apply u h w a, hw, AddMonoidHom.zero_apply]
  have hDs : fderiv ℂ (fun z => valAt' (u.ex z).left U (s : Γ(A.left, U))) 0 w = 0 := by
    rw [← dirDeriv_apply u h w (s : Γ(A.left, U)), hw, AddMonoidHom.zero_apply]

  have hs0 : valAt' (u.ex 0).left U (s : Γ(A.left, U)) ≠ 0 := by
    obtain ⟨v, hv⟩ := IsLocalization.map_units Γ(A.left, A.left.basicOpen b) s
    rw [← hres 0 hb0, ← hv]
    intro h0
    have hone := valAt'_mul (u.ex 0).left (A.left.basicOpen b) (v : Γ(A.left, A.left.basicOpen b))
      (↑v⁻¹ : Γ(A.left, A.left.basicOpen b))
    have h1 : valAt' (u.ex 0).left (A.left.basicOpen b) (1 : Γ(A.left, A.left.basicOpen b)) = 1 := by
      exact valAt'_one _ hb0
    rw [Units.mul_inv, h1, h0, zero_mul] at hone
    exact one_ne_zero hone

  have hmul := fderiv_fun_mul (differentiableAt_val u hV f) (differentiableAt_val u h (s : Γ(A.left, U)))
  rw [hev.fderiv_eq] at hmul
  have key := congrArg (fun L => L w) hmul
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hDa, hDs,
    mul_zero, zero_add] at key
  exact (mul_eq_zero.1 key.symm).resolve_left hs0
end GlobalTheory.AdaptedCoord
