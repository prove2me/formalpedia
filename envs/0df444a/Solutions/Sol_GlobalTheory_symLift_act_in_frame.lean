-- Prove2me | solution 1 for GlobalTheory.symLift_act_in_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:48.262732+00:00
-- url     : https://prove2.me/submissions/3f588e72-c391-48ec-9fba-73cfb82ed891

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
import Theorems.Thm_GlobalTheory_SymLiftFrame_mem_chart
import Theorems.Thm_GlobalTheory_SymLiftFrame_exists_choice
import Theorems.Thm_GlobalTheory_SymLiftFrame_pow_mul_eq_one
import Theorems.Thm_GlobalTheory_SymLiftFrame_sq_eq_one
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_right
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translPt
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translT
import Theorems.Thm_GlobalTheory_ThetaFn_exists_hasAnConst
import Theorems.Thm_GlobalTheory_semicharacter_sq_eq_one_of_symmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
section Values
variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
private theorem valAt'_presheaf_map_homOfLE {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Z, U)) :
    valAt' x V (Z.presheaf.map (homOfLE hVU).op f) = valAt' x U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (h.trans fun p hp => hVU hp)]
  unfold valAt
  congr 1
  rw [← Scheme.Hom.map_appLE x h (homOfLE hVU).op]
  rfl
private theorem valAt'_mul_moduli {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f f' : Γ(Z, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  unfold valAt'
  split_ifs with h
  · unfold valAt
    rw [map_mul, map_mul]
  · rw [zero_mul]
private theorem valAt'_app_eq_valAt'_comp' {Z Z' : Scheme.{0}} (x : Sp ℂ ⟶ Z') (q : Z' ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valAt' x (q ⁻¹ᵁ U) (q.app U f) = valAt' (x ≫ q) U f := by
  unfold valAt'
  rw [dif_pos h, dif_pos (show ⊤ ≤ x ⁻¹ᵁ q ⁻¹ᵁ U from h)]
  unfold valAt
  congr 1
variable {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
end Values
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}
end GlobalTheory.SymLiftFrame
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.SymLiftFrame GlobalTheory.ThetaFn GlobalTheory.AppellHumbertTrivial
namespace GlobalTheory
theorem _root_.solution : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  intro _ _ _ _ P u Hm χ N l f T _ p x U s s' hAH hN hx hS hAct hs j z hz
  obtain ⟨J, hJ⟩ := exists_choice P.isLB
  obtain ⟨hpteq, hpow, nu, hnu, hsym⟩ := hS
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_ne_zero (by rintro rfl; exact absurd hN (by decide))).ne'
  set x0 : Fin P.g → ℂ := ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ) with hx0
  have hpt0 : p ≫ U.pt = u.ex x0 := by rw [hpteq, hx]
  obtain ⟨c, hc⟩ := (exists_hasAnConst P.isLB hAH hpt0).2
  have hl' : ((N ^ 2 : ℕ) : ℂ) • x0 = l := by
    rw [hx0, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hN0), one_smul]
  have hpowc := pow_mul_eq_one P.isLB hAH hc hl' hpow
  have hsq := sq_eq_one P.isLB hAH hc hnu hsym
  have hχ := GlobalTheory.semicharacter_sq_eq_one_of_symmetric P u Hm χ hAH l
  obtain ⟨m, hm⟩ : Odd (N ^ 2) := hN.pow
  rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hm, pow_succ, pow_succ,
    pow_mul, pow_mul, hsq, hχ] at hpowc
  simp only [one_pow, _root_.one_mul] at hpowc
  have hcχ : c = χ l := by linear_combination (χ l) * hpowc - c * hχ
  obtain ⟨j0, rfl⟩ : ∃ j0, j = fun _ => j0 := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hsnd : ∀ w, exAt u p w ≫ (snd T P.A).left = (u.ex w).left := fun w => by
    show (lift p (u.ex w)).left ≫ (snd T P.A).left = _
    rw [← Over.comp_left, lift_snd]
  have hW : ∀ w, ⊤ ≤ exAt u p w ⁻¹ᵁ
      LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => J (u.ex w).left) := fun w => by
    have h1 := mem_chart hJ (fun _ : Fin 1 => (snd T P.A).left) (exAt u p w)
    simp only [hsnd] at h1
    exact h1
  have htr : exAt u p z ≫ (Out.translPt P.A U.pt).left = (u.ex (z + x0)).left := exAt_translPt u hpt0 z
  have hV : ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
      ![j0, J (u.ex (z + x0)).left] :=
    (exAt_mem_pairChart_iff htr _).2 ⟨hz, hJ _⟩
  have e := congrArg (valAt' (exAt u p z) _) (hAct ![j0, J (u.ex (z + x0)).left])
  have e2 : valAt' (exAt u p z) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => j0) (s'.f fun _ => j0) =
      valAt' (exAt u p z) (LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
        ![j0, J (u.ex (z + x0)).left]) (U.φ.s ![j0, J (u.ex (z + x0)).left]).val *
      valAt' (exAt u p (z + x0)) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => J (u.ex (z + x0)).left)
        (s.f fun _ => J (u.ex (z + x0)).left) := by
    refine (valAt'_presheaf_map_homOfLE _ _ hV _).symm.trans (e.trans ((valAt'_mul_moduli _ _ _ _).trans ?_))
    refine congrArg₂ (· * ·) rfl ?_
    refine (valAt'_presheaf_map_homOfLE _ _ hV _).trans ?_
    refine (valAt'_app_eq_valAt'_comp' _ _ _ ?_ _).trans ?_
    · rw [exAt_translT u hpt0 z]
      exact hW _
    · rw [exAt_translT u hpt0 z]
      rfl
  have hs' : valAt' (exAt u p (z + x0)) ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U fun _ => J (u.ex (z + x0)).left)
      (s.f fun _ => J (u.ex (z + x0)).left) = f (z + x0) * u.fr (J (u.ex (z + x0)).left) (z + x0) ^ ((N : ℤ) ^ 2) :=
    hs _ _ (hJ _)
  have hc2 : valAt' (exAt u p z) (LB.wchart P.L ![(snd T P.A).left, (Out.translPt P.A U.pt).left]
        ![j0, J (u.ex (z + x0)).left]) (U.φ.s ![j0, J (u.ex (z + x0)).left]).val *
      u.fr (J (u.ex (z + x0)).left) (z + x0) ^ ((N : ℤ) ^ 2) =
      c * fockFactor Hm ((N : ℤ) ^ 2) x0 z * u.fr j0 z ^ ((N : ℤ) ^ 2) := hc.2 _ z hz (hJ _)
  have hfock : fockFactor Hm ((N : ℤ) ^ 2) x0 z =
      Complex.exp (-((Real.pi : ℂ) / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - (Real.pi : ℂ) * hermForm Hm z l) := by
    unfold fockFactor
    congr 1
    rw [hx0]
    simp only [hermForm_smul_left, hermForm_smul_right, star_inv₀, star_pow, star_natCast]
    push_cast
    field_simp
    ring
  refine e2.trans ?_
  rw [hs']
  show _ = χ l * _ * f (z + x0) * u.fr j0 z ^ ((N : ℤ) ^ 2)
  linear_combination f (z + x0) * hc2 + (fockFactor Hm ((N : ℤ) ^ 2) x0 z * f (z + x0) *
    u.fr j0 z ^ ((N : ℤ) ^ 2)) * hcχ + (χ l * f (z + x0) * u.fr j0 z ^ ((N : ℤ) ^ 2)) * hfock
end GlobalTheory
