-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_linear_of_first_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:26.278736+00:00
-- url     : https://prove2.me/submissions/a6fcbe00-63c3-449e-b299-651fe6921909

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TranslationFixingBundleArtinPointEqOne
import Theorems.Thm_GlobalTheory_ArtinKernel_log_deriv_rule
import Theorems.Thm_GlobalTheory_ArtinKernel_differentiableOn_famPt
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_const
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_gen_two
import Theorems.Thm_GlobalTheory_ArtinKernel_ex_add_lattice
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_linear_of_log_deriv
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_mem
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_snd
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_transl
import Theorems.Thm_GlobalTheory_ArtinKernel_first_order_transl
import Theorems.Thm_GlobalTheory_ArtinKernel_residue_evalPt
import Theorems.Thm_GlobalTheory_ArtinKernel_residue_transl
import Theorems.Thm_GlobalTheory_ArtinKernel_snd_preimage_le
import Theorems.Thm_GlobalTheory_ArtinKernel_subsingleton_primeSpectrum
import Theorems.Thm_GlobalTheory_ArtinKernel_top_le_const
import Theorems.Thm_GlobalTheory_ArtinKernel_top_le_iff_residue
import Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_inf
import Theorems.Thm_P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c
import Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__unit_ne_zero_1f417e79e6fc
import Theorems.Thm_P2M_GlobalTheory_valAt__unit_ne_zero_54a31b83d959


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ))
    (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ)
    (hκ : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
    (c : LB.Gen (Out.translDiff A L x)) (hc : c.IsGen) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, B l w = lam l := by
  have hsub := subsingleton_primeSpectrum (R := R)
  have hle := snd_preimage_le (L := L) ρ x hx
  have hD : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      ⊤ ≤ (famPt u R z).left ⁻¹ᵁ (Out.translDiff A L x).U (fun _ => i) :=
    fun i z hz => le_trans (famPt_mem (R := R) u z hz) ((famPt u R z).left.preimage_mono (hle i))
  obtain ⟨F, hFdef⟩ : ∃ F : L.ι → (Fin g → ℂ) → R, ∀ i z,
      F i z = evalPt' (R := R) (famPt u R z).left _ (c.s (fun _ => i)).val :=
    ⟨fun i z => evalPt' (R := R) (famPt u R z).left _ (c.s (fun _ => i)).val, fun _ _ => rfl⟩
  have hF : ∀ i (lam : R →ₗ[ℂ] ℂ),
      DifferentiableOn ℂ (fun z => lam (F i z)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} := fun i lam => by
    simp only [hFdef]
    exact differentiableOn_famPt u (hle i) _ lam
  have hF0 : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ρ (F i z) ≠ 0 := fun i z hz => by
    rw [hFdef, evalPt'_eq _ (hD i z hz)]
    exact (((c.s (fun _ => i)).isUnit.map _).map ρ).ne_zero
  refine exists_linear_of_log_deriv u hL a B ha hfr w (fun i z => κ (F i z) * (ρ (F i z))⁻¹)
    (fun i => (hF i κ).mul ((hF i ρ.toLinearMap).inv (hF0 i))) (fun i z l hl => ?_) (fun i i' z hz hz' => ?_)
  · have : F i (z + l) = F i z := by
      rw [hFdef, hFdef, famPt, famPt, ex_add_lattice u z hl]
    simp only [this]
  · have a1 := ThetaGroupFrame.top_le_inf _ hz hz'
    have a0 : ⊤ ≤ (x ≫ translBy u z).left ⁻¹ᵁ (L.U i ⊓ L.U i') :=
      (top_le_iff_residue ρ.toRingHom _ _ (residue_transl u ρ x hx z) _).2 a1
    have e := evalPt_gen_two (R := R) L _ _ c hc _ _ _ (famPt_transl u x z) (famPt_snd u z)
      (fun _ => i) (fun _ => i') (hD i z hz) (hD i' z hz') a0 (top_le_const _ _ a1)
    have hρ : ρ (evalPt (R := R) (x ≫ translBy u z).left _ a0 (L.g i i').val) = _ :=
      residue_evalPt ρ.toRingHom _ _ (residue_transl u ρ x hx z) _ a0 (L.g i i').val
    have k := first_order_transl u ρ x κ w hκ z _ a0 (L.g i i').val (F i' z)
    have e' : F i z * algebraMap ℂ R (valAt' (u.ex z).left _ (L.g i i').val) =
        evalPt (R := R) (x ≫ translBy u z).left _ a0 (L.g i i').val * F i' z := by
      rw [hFdef, hFdef, evalPt'_eq _ (hD i z hz), evalPt'_eq _ (hD i' z hz'),
        ← evalPt_const (R := R) _ _ (top_le_const _ _ a1) a1]
      exact e
    have n0 := valAt'_unit_ne_zero _ a1 (L.g i i')
    have n2 := hF0 i' z hz'
    exact log_deriv_rule ρ κ e' hρ k n0 n2
end GlobalTheory.ArtinKernel
