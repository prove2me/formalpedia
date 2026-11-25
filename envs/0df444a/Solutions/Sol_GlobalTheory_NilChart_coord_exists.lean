-- Prove2me | solution 1 for GlobalTheory.NilChart.coord_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:38.770551+00:00
-- url     : https://prove2.me/submissions/7ad5f604-e561-4010-b8c7-104069571ec0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_GlobalTheory_NilChart_mk_comp_eq
import Theorems.Thm_GlobalTheory_NilChart_move
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_existsUnique_eq_lieExp_mul
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃ ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  have haug : spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
    have e : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
      (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
    rw [e, ← spMap_comp, Category.assoc, hx₂ m, comp_one']
  have fac : ∀ {A₁ A₂ : Type} [CommRing A₁] [Algebra R A₁] [CommRing A₂] [Algebra R A₂] (p : B →ₐ[R] A₁)
      (q : A₁ →ₐ[R] A₂) {y y' : sp (R₀ := R) B ⟶ G}, spMap p ≫ y = spMap p ≫ y' →
      spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := fun p q y y' h => by
    rw [← spMap_comp, Category.assoc, Category.assoc, h]
  have key : ∀ k : ℕ, ∃ (b : Fin d → B) (hb : ∀ j, b j ∈ N),
      spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ y =
        spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ spMap (jetLift R _ hN b hb) ≫ x m := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => zero_mem _, ?_⟩
      have e : Ideal.Quotient.mkₐ R (N ^ (0 + 1)) =
          (Ideal.Quotient.factorₐ R (show N ≤ N ^ (0 + 1) by rw [zero_add, pow_one])).comp
            (Ideal.Quotient.mkₐ R N) := by
        ext a; rfl
      rw [e]
      refine fac _ _ ?_
      rw [hy, ← Category.assoc, spMap_comp, mk_comp_eq _ (fun j => by rw [jetLift_zR]; exact zero_mem _),
        ← spMap_comp, Category.assoc, haug, comp_one']
    | succ k ih =>
      obtain ⟨b, hb, ih⟩ := ih
      let B' := B ⧸ N ^ (k + 1 + 1)
      let π : B →ₐ[R] B' := Ideal.Quotient.mkₐ R (N ^ (k + 1 + 1))
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let J : Ideal B' := (N ^ (k + 1)).map π
      have hJN : J * N.map π = ⊥ := by
        rw [← Ideal.map_mul, ← pow_succ]
        exact Ideal.map_quotient_self _
      have hJle : J ≤ N.map π := Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hJ : J ^ 2 = ⊥ := by
        rw [← le_bot_iff, pow_two, ← hJN]
        exact Ideal.mul_mono_right hJle
      let q : (B ⧸ N ^ (k + 1)) →ₐ[R] B' ⧸ J := Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ R J).comp π)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
      have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (k + 1))) = (Ideal.Quotient.mkₐ R J).comp π := by
        ext a; rfl
      have h2 := fac _ q ih
      rw [hq, ← spMap_comp, Category.assoc, Category.assoc] at h2
      haveI := hG
      obtain ⟨c, hc, -⟩ := SqZero.existsUnique_eq_lieExp_mul hv hJ h2.symm
      choose δ hδ hδc using fun j => (Ideal.mem_map_iff_of_surjective π hπ).1 (c j).2
      have hb' : ∀ j, b j + δ j ∈ N := fun j =>
        add_mem (hb j) (Ideal.pow_le_self (by omega) (hδ j))
      refine ⟨fun j => b j + δ j, hb', ?_⟩
      have h3 := move hG hv hx₁ hx₂ hx₃ hJN hJle
        (π.comp (jetLift R _ hN b hb)) (π.comp (jetLift R _ hN (fun j => b j + δ j) hb'))
        (fun j => by rw [AlgHom.comp_apply, jetLift_zR]; exact Ideal.mem_map_of_mem _ (hb j))
        (fun j => (c j : B')) (fun j => (c j).2) (fun j => SqZero.mul_eq_zero_of_sq hJ (c j).2 (c j).2)
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, jetLift_zR, jetLift_zR, map_add, hδc])
      change spMap π ≫ y = spMap π ≫ _
      rw [hc, ← Category.assoc, spMap_comp, ← Category.assoc, spMap_comp, h3]
  obtain ⟨b, hb, h⟩ := key m
  refine ⟨jetLift R _ hN b hb, ?_⟩
  let q : (B ⧸ N ^ (m + 1)) →ₐ[R] B := Ideal.Quotient.liftₐ _ (AlgHom.id R B)
    (fun a ha => by rw [hN] at ha; exact ha)
  have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (m + 1))) = AlgHom.id R B := by
    ext a; rfl
  have h2 := fac _ q h
  rw [hq, spMap_id, Category.id_comp, Category.id_comp] at h2
  exact h2.symm
end GlobalTheory.NilChart
