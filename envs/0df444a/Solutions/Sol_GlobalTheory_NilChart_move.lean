-- Prove2me | solution 1 for GlobalTheory.NilChart.move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:38.147798+00:00
-- url     : https://prove2.me/submissions/7dca8985-4bce-4ff4-b403-0a4b060dfa7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_GlobalTheory_NilChart_mem_augAlg
import Theorems.Thm_GlobalTheory_NilChart_mk_comp_eq
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_jet_add_sqZero_eq_prod_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilChart
open SqZero
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
include hG hv hx₁ hx₂ hx₃
namespace GlobalTheory.NilChart
theorem _root_.solution {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (c : Fin d → B) (hcJ : ∀ j, c j ∈ J) (hc : ∀ j, c j * c j = 0)
    (h : ∀ j, ψ' (zR m j) = ψ (zR m j) + c j) : spMap ψ' ≫ x m = lieExp v c hc * (spMap ψ ≫ x m) := by
  have hψ' : ∀ j, ψ' (zR m j) ∈ I := fun j => by rw [h]; exact add_mem (hψ j) (hle (hcJ j))
  let aug : augAlg R I →ₐ[R] R := (AlgHom.fst R R B).comp (augAlg R I).val
  let p : augAlg R I →ₐ[R] B := (AlgHom.snd R R B).comp (augAlg R I).val
  let up : ∀ φ : JetR R (Fin d) m →ₐ[R] B, (∀ j, φ (zR m j) ∈ I) → (JetR R (Fin d) m →ₐ[R] augAlg R I) :=
    fun φ hφ => ((jetAug R (Fin d) m).prod φ).codRestrict _ fun a => by
      have := AlgHom.congr_fun (mk_comp_eq φ hφ) a
      exact this
  let J' : Ideal (augAlg R I) := J.comap p ⊓ RingHom.ker aug
  have hker : ∀ a : augAlg R I, a ∈ RingHom.ker aug → p a ∈ I := fun a ha => by
    have h1 : a.1.1 = 0 := ha
    have h2 := mem_augAlg.1 a.2
    rw [h1, map_zero, sub_zero] at h2
    exact h2
  have hJ' : J' * RingHom.ker aug = ⊥ := by
    rw [← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have h1 : a.1.1 = 0 := ha.2
    have h2 : p a * p b ∈ J * I := Ideal.mul_mem_mul ha.1 (hker b hb)
    rw [hJ] at h2
    exact Subtype.ext (Prod.ext (show a.1.1 * b.1.1 = 0 by rw [h1, zero_mul]) h2)
  let c' : Fin d → augAlg R I := fun j => ⟨(0, c j), mem_augAlg.2 (by simpa using hle (hcJ j))⟩
  have hc' : ∀ j, c' j * c' j = 0 := fun j => Subtype.ext (Prod.ext (mul_zero _) (hc j))
  have he : ∀ j, epsTo R (c' j) (hc' j) (TrivSqZeroExt.inr 1) = c' j := fun j => epsTo_eps _ _
  have key := jet_add_sqZero_eq_prod_mul R G hG d v hv x hx₁ hx₂ hx₃ _ aug J' hJ' inf_le_right m
    (up ψ hψ) (up ψ' hψ') rfl rfl (fun j => epsTo R (c' j) (hc' j))
    (fun j => by rw [he]; exact ⟨hcJ j, rfl⟩)
    (fun j => by
      rw [he]
      exact Subtype.ext (Prod.ext (add_zero _).symm (h j)))
  have fin := congrArg (spMap p ≫ ·) key
  change spMap p ≫ spMap _ ≫ x m = spMap p ≫ (lieExp v c' hc' * (spMap _ ≫ x m)) at fin
  rw [MonObj.comp_mul, comp_lieExp, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp] at fin
  exact fin
end GlobalTheory.NilChart
