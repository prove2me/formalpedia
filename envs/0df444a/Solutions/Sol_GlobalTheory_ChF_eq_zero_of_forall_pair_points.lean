-- Prove2me | solution 1 for GlobalTheory.ChF.eq_zero_of_forall_pair_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:21.521608+00:00
-- url     : https://prove2.me/submissions/57c5437d-e531-41f2-b332-0037ee5549e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfForallPairPointsValuationIntegers
import Theorems.Thm_GlobalTheory_ChF_mem_sup_span_X_pow_iff_and_isAdicComplete
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvPowerSeries_eval_of_pow_mem
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X


section
namespace GlobalTheory.ChF
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section
variable {O : Type} [CommRing O] {d : ℕ}
private theorem exists_algHom_ev (j : Fin 2) : ∃ E : PS O 1 d →ₐ[O] PS O 2 d,
    (∀ u, E u = ev (n := 2) ![pt O d j] u) ∧ ∀ q, E (X q) = X (j, q.2) := by
  have h : HasSubst (fun q : Fin 1 × Fin d => (![pt O d j] : Fin 1 → Pt O 2 d) q.1 q.2) :=
    hasSubst_of_constantCoeff_zero fun q => by simp [pt, Matrix.cons_val_fin_one]
  refine ⟨substAlgHom h, fun u => by rw [coe_substAlgHom]; rfl, fun q => ?_⟩
  rw [coe_substAlgHom, subst_X h]
  simp [pt, Matrix.cons_val_fin_one]
private theorem exists_ringHom_eval {A B σ : Type} [CommRing A] [CommRing B] [Finite σ]
    (J : Ideal B) (hJ : IsAdicComplete J B) (E : A →+* B) (b : σ → B)
    (hb : ∀ q, ∃ M : ℕ, b q ^ M ∈ J) :
    ∃ T : MvPowerSeries σ A →+* B, (∀ u, T (C u) = E u) ∧ ∀ q, T (X q) = b q := by
  letI : Algebra A B := E.toAlgebra
  obtain ⟨T, hT⟩ := (mvPowerSeries_eval_of_pow_mem B J σ b hb).1 hJ A
  exact ⟨T.toRingHom, fun u => T.commutes u, hT⟩
private theorem exists_curry :
    ∃ S : PS O 2 d →ₐ[O] MvPowerSeries (Fin 1 × Fin d) (PS O 1 d), Function.Injective S ∧
      (∀ u, S (ev (n := 2) ![pt O d 0] u) = MvPowerSeries.map (C : O →+* PS O 1 d) u) ∧
      ∀ u, S (ev (n := 2) ![pt O d 1] u) = C u := by
  obtain ⟨E₀, hE₀, hX₀⟩ := exists_algHom_ev (O := O) (d := d) 0
  obtain ⟨E₁, hE₁, hX₁⟩ := exists_algHom_ev (O := O) (d := d) 1
  have hA := (mem_sup_span_X_pow_iff_and_isAdicComplete O ⊥ (Fin 1 × Fin d)).2 inferInstance
  have hP := (mem_sup_span_X_pow_iff_and_isAdicComplete O ⊥ (Fin 2 × Fin d)).2 inferInstance
  have hB := (mem_sup_span_X_pow_iff_and_isAdicComplete (PS O 1 d) _ (Fin 1 × Fin d)).2 hA
  set I : Ideal (PS O 1 d) := (⊥ : Ideal O).map (C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (X : Fin 1 × Fin d → PS O 1 d)) with hI
  set J : Ideal (PS O 2 d) := (⊥ : Ideal O).map (C : O →+* PS O 2 d) ⊔
    Ideal.span (Set.range (X : Fin 2 × Fin d → PS O 2 d)) with hJ
  set K : Ideal (MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) := I.map C ⊔
    Ideal.span (Set.range X) with hK
  have hXK : ∀ q : Fin 1 × Fin d, ∃ M : ℕ,
      (X q : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) ^ M ∈ K := fun q =>
    ⟨1, by rw [pow_one]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)⟩
  have hCK : ∀ q : Fin 1 × Fin d, ∃ M : ℕ,
      (C (X q) : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) ^ M ∈ K := fun q =>
    ⟨1, by
      rw [pow_one]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)))⟩
  have hXJ : ∀ q : Fin 2 × Fin d, ∃ M : ℕ, (X q : PS O 2 d) ^ M ∈ J := fun q =>
    ⟨1, by rw [pow_one]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)⟩
  obtain ⟨S, hS⟩ := (mvPowerSeries_eval_of_pow_mem _ K (Fin 2 × Fin d)
    (fun q => if q.1 = 0 then X (0, q.2) else C (X (0, q.2))) fun q => by
      split_ifs
      exacts [hXK _, hCK _]).1 hB O
  have hq : ∀ q : Fin 1 × Fin d, ((0 : Fin 1), q.2) = q := fun q =>
    Prod.ext (Subsingleton.elim _ _) rfl
  have hc : ∀ t : O, algebraMap O (MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) t = C (C t) :=
    fun t => MvPowerSeries.algebraMap_apply
  have h0 : S.toRingHom.comp E₀.toRingHom = MvPowerSeries.map (C : O →+* PS O 1 d) := by
    refine (mvPowerSeries_eval_of_pow_mem _ K (Fin 1 × Fin d) X hXK).2 inferInstance O _ _
      (fun t => ?_) (fun q => ?_) (fun q => map_X _ q)
    · rw [map_C]
      exact ((S.comp E₀).commutes t).trans (hc t)
    · change S (E₀ (X q)) = _
      rw [hX₀, hS, if_pos rfl, hq]
  have h1 : S.toRingHom.comp E₁.toRingHom = C := by
    refine (mvPowerSeries_eval_of_pow_mem _ K (Fin 1 × Fin d) (fun q => C (X q)) hCK).2
      inferInstance O _ _ (fun t => ?_) (fun q => ?_) (fun q => rfl)
    · exact ((S.comp E₁).commutes t).trans (hc t)
    · change S (E₁ (X q)) = _
      rw [hX₁, hS, if_neg (by simp), hq]
  refine ⟨S, ?_, fun u => ?_, fun u => ?_⟩
  · obtain ⟨T, hTC, hTX⟩ : ∃ T : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d) →+* PS O 2 d,
        (∀ u, T (C u) = E₁ u) ∧ ∀ q, T (X q) = X (0, q.2) :=
      exists_ringHom_eval J hP E₁.toRingHom _ fun q => hXJ _
    have hTS : T.comp S.toRingHom = RingHom.id _ := by
      refine (mvPowerSeries_eval_of_pow_mem _ J (Fin 2 × Fin d) X hXJ).2 inferInstance O _ _
        (fun t => ?_) (fun q => ?_) (fun q => rfl)
      · change T (S (algebraMap O _ t)) = _
        rw [S.commutes, hc]
        exact (hTC (C t)).trans (E₁.commutes t)
      · change T (S (X q)) = _
        obtain ⟨j, i⟩ := q
        rw [hS]
        fin_cases j
        · simp [hTX]
        · simp [hTC, hX₁]
    exact Function.LeftInverse.injective (g := T) fun f => DFunLike.congr_fun hTS f
  · rw [← hE₀]
    exact DFunLike.congr_fun h0 u
  · rw [← hE₁]
    exact DFunLike.congr_fun h1 u
end
end GlobalTheory.ChF
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {O : Type} [CommRing O] {d : ℕ}
namespace GlobalTheory.ChF
theorem _root_.solution (W : (PS O 1 d →ₐ[O] O) → Prop)
    (hW : ∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) (f : PS O 2 d)
    (hf : ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O),
      (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) →
        W φ → W φ' → Φ f = 0) : f = 0 := by
  obtain ⟨S, hS, h0, h1⟩ := exists_curry (O := O) (d := d)
  refine hS ?_
  rw [map_zero]
  ext1 e
  rw [map_zero]
  refine hW _ fun φ' hφ' => ?_
  have hC : φ'.toRingHom.comp (C : O →+* PS O 1 d) = RingHom.id O :=
    RingHom.ext fun t => φ'.commutes t
  have key : MvPowerSeries.map φ'.toRingHom (S f) = 0 := by
    refine hW _ fun φ hφ => ?_
    refine hf (φ.comp ((MvPowerSeries.mapAlgHom φ').comp S)) φ φ' (fun u => ?_) (fun u => ?_)
      hφ hφ'
    · change φ (MvPowerSeries.map φ'.toRingHom (S _)) = _
      rw [h0, ← RingHom.comp_apply, ← MvPowerSeries.map_comp, hC, MvPowerSeries.map_id]
      rfl
    · change φ (MvPowerSeries.map φ'.toRingHom (S _)) = _
      rw [h1, map_C]
      exact φ.commutes _
  have := congrArg (coeff e) key
  rwa [coeff_map, map_zero] at this
end GlobalTheory.ChF
