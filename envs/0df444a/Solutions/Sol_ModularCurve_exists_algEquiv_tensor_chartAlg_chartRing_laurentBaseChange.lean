-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/484c2f2c-24c6-5c1a-bb65-9ea84335171f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

open ModularCurve AlgebraicCurve
open scoped TensorProduct

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace CC2B01K2B

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve.CurveModel

section Emb

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)]

private def emb : ↥F₀ →+* (laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
  ((coeffEmb (AlgebraicClosure ℚ)).comp (SubringClass.subtype F₀)).codRestrict
    (laurentBaseChange (AlgebraicClosure ℚ) F₀)
    fun x => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2

private theorem emb_apply (x : ↥F₀) :
    emb F₀ x = ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := rfl

private theorem emb_jFull_inv : emb F₀ j⁻¹ = (emb F₀ j)⁻¹ := map_inv₀ _ _

private theorem jBar_ne_zero : (emb F₀ j) ≠ 0 := (map_ne_zero (emb F₀)).mpr Fact.out

private scoped instance factJBarNeZero : Fact ((emb F₀ j) ≠ 0) := ⟨jBar_ne_zero F₀ j⟩

end Emb

private theorem ringHom_apply_eq_ratCast {S : Subring ℚ} {R : Type*} [DivisionRing R] [Algebra ℚ R]
    (f : ↥S →+* R) (q : ↥S) : f q = ((q : ℚ) : R) := by
  have hd : (((q : ℚ).den : ℕ) : R) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ R)]
    exact (map_ne_zero (algebraMap ℚ R)).mpr (Nat.cast_ne_zero.mpr (q : ℚ).den_ne_zero)
  have hmul : f q * (((q : ℚ).den : ℕ) : R) = (((q : ℚ).num : ℤ) : R) := by
    rw [← map_natCast f, ← map_intCast f, ← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (q : ℚ)
  rw [Rat.cast_def, eq_div_iff hd, hmul]

section Charts

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

private theorem emb_mem_adjoin {S : Set ↥F₀} {T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)}
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) {x : ↥F₀}
    (hx : x ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S) :
    emb F₀ x ∈ Algebra.adjoin (AlgebraicClosure ℚ) T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      have h : emb F₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r) =
          ((r : ℚ) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
        ringHom_apply_eq_ratCast ((emb F₀).comp
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀)) r
      rw [h, ← map_ratCast (algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀))]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem emb_mem_chartRing {S : Set ↥F₀} {T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)}
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) {b : ↥F₀} (hb : b ∈ chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) :
    emb F₀ b ∈ chartRing (AlgebraicClosure ℚ) T := by
  have hint : IsIntegral (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S) b :=
    hb
  let ψ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S) →+* ↥(Algebra.adjoin (AlgebraicClosure ℚ) T) :=
    ((emb F₀).comp (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S).val.toRingHom).codRestrict
      (Algebra.adjoin (AlgebraicClosure ℚ) T).toSubring fun x => emb_mem_adjoin F₀ p hST x.2
  exact IsIntegral.map_of_comp_eq ψ (emb F₀) (RingHom.ext fun _ => rfl) hint

private def ρ (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) →+* ↥(chartRing (AlgebraicClosure ℚ) T) where
  toFun b := ⟨emb F₀ b, emb_mem_chartRing F₀ p hST b.2⟩
  map_one' := Subtype.ext (by simp only [Subalgebra.coe_one, map_one])
  map_mul' a b := Subtype.ext (by simp only [Subalgebra.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [Subalgebra.coe_zero, map_zero])
  map_add' a b := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])

private theorem coe_ρ_apply (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    (ρ F₀ p S T hST b : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b := rfl

private theorem ρ_comp_algebraMap (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (ρ F₀ p S T hST).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) =
      (algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
  refine RingHom.ext fun q => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_ρ_apply]
  have h1 : emb F₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ q) =
      ((q : ℚ) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
    ringHom_apply_eq_ratCast ((emb F₀).comp
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀)) q
  have h2 : algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) q =
      ((q : ℚ) : AlgebraicClosure ℚ) :=
    ringHom_apply_eq_ratCast (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) q
  rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, h1, h2, map_ratCast]

private theorem fin_sub : ∀ s ∈ ({j} : Set ↥F₀),
    emb F₀ s ∈ ({(emb F₀ j)} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs]

private theorem inf_sub : ∀ s ∈ ({j⁻¹} : Set ↥F₀),
    emb F₀ s ∈ ({(emb F₀ j)⁻¹} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_jFull_inv]

private theorem mid_sub : ∀ s ∈ ({j, j⁻¹} : Set ↥F₀),
    emb F₀ s ∈ ({(emb F₀ j), (emb F₀ j)⁻¹} :
      Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) := by
  intro s hs
  rcases hs with rfl | hs
  · exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff] at hs
    rw [hs, emb_jFull_inv]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private abbrev ρFin : ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(emb F₀ j)} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))) :=
  ρ F₀ p _ _ (fin_sub F₀ j)

private abbrev ρInf : ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(emb F₀ j)⁻¹} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))) :=
  ρ F₀ p _ _ (inf_sub F₀ j)

private abbrev ρMid : ↥(chartAlgMid ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(emb F₀ j),
      (emb F₀ j)⁻¹} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))) :=
  ρ F₀ p _ _ (mid_sub F₀ j)

private theorem jb_subset_pair : ({(emb F₀ j)} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) ⊆
    {(emb F₀ j), (emb F₀ j)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem jb_inv_subset_pair :
    ({(emb F₀ j)⁻¹} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) ⊆
      {(emb F₀ j), (emb F₀ j)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem square_fin :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_subset_pair F₀ j)).toRingHom.comp (ρFin F₀ j p) =
      (ρMid F₀ j p).comp (AlgebraicCurve.TwoChartIntegralModel.inclFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl]

private theorem square_inf :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_inv_subset_pair F₀ j)).toRingHom.comp (ρInf F₀ j p) =
      (ρMid F₀ j p).comp (AlgebraicCurve.TwoChartIntegralModel.inclInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl]

end Charts

section Tensor

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

local instance instAlgebraRatLocalizedChartRing (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(chartRing (AlgebraicClosure ℚ) T) :=
  ((algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp
    (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).toAlgebra

set_option synthInstance.maxHeartbeats 1600000 in

private def ρAlg (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { ρ F₀ p S T hST with
    commutes' := fun q => RingHom.congr_fun (ρ_comp_algebraMap F₀ p S T hST) q }

set_option synthInstance.maxHeartbeats 1600000 in

private def incAlg (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) with
    commutes' := fun _ => rfl }

set_option synthInstance.maxHeartbeats 1600000 in

private def θ (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) ⊗[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) →+*
      ↥(chartRing (AlgebraicClosure ℚ) T) :=
  (Algebra.TensorProduct.lift (ρAlg F₀ p S T hST) (incAlg F₀ p T) fun _ _ => Commute.all _ _).toRingHom

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) (c : AlgebraicClosure ℚ) :
    θ F₀ p S T hST (b ⊗ₜ c) = ρ F₀ p S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  Algebra.TensorProduct.lift_tmul (ρAlg F₀ p S T hST) (incAlg F₀ p T) _ b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem coe_θ_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) (c : AlgebraicClosure ℚ) :
    ((θ F₀ p S T hST (b ⊗ₜ c) : ↥(chartRing (AlgebraicClosure ℚ) T)) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
      c • emb F₀ b := by
  rw [θ_tmul, Subalgebra.coe_mul, coe_ρ_apply, Algebra.smul_def, mul_comm]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeLeft (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (θ F₀ p S T hST).comp Algebra.TensorProduct.includeLeftRingHom = ρ F₀ p S T hST := by
  refine RingHom.ext fun b => ?_
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θ_tmul, map_one, mul_one]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeRight (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (θ F₀ p S T hST).comp
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt p)]
            ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) ⊗[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) := by
  refine RingHom.ext fun c => ?_
  simpa using θ_tmul F₀ p S T hST 1 c

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θFin := θ F₀ p _ _ (fin_sub F₀ j)

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θInf := θ F₀ p _ _ (inf_sub F₀ j)

end Tensor

section TensorLeft

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

private abbrev cm (S : Set ↥F₀) :=
  Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private def θL (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) where
  toRingHom := (θ F₀ p S T hST).comp (cm F₀ p S : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ≃+* _).toRingHom
  commutes' c := by
    show θ F₀ p S T hST ((1 : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ⊗ₜ c) = algebraMap (AlgebraicClosure ℚ) _ c
    rw [θ_tmul, map_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_apply (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (x : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S))) :
    θL F₀ p S T hST x = θ F₀ p S T hST (cm F₀ p S x) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (c : AlgebraicClosure ℚ) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    θL F₀ p S T hST (c ⊗ₜ b) = ρ F₀ p S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  θ_tmul F₀ p S T hST b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_one_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    θL F₀ p S T hST (1 ⊗ₜ b) = ρ F₀ p S T hST b := by
  rw [θL_tmul, map_one, mul_one]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem coe_θL_one_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    ((θL F₀ p S T hST (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b := by
  rw [θL_one_tmul, coe_ρ_apply]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_injective (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (h : Function.Injective (θ F₀ p S T hST)) :
    Function.Injective (θL F₀ p S T hST) := fun x y hxy =>
  (cm F₀ p S).injective (h (by rwa [θL_apply, θL_apply] at hxy))

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_surjective (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (h : Function.Surjective (θ F₀ p S T hST)) :
    Function.Surjective (θL F₀ p S T hST) := fun z => by
  obtain ⟨w, hw⟩ := h z
  exact ⟨(cm F₀ p S).symm w, by rw [θL_apply, (cm F₀ p S).apply_symm_apply, hw]⟩

set_option synthInstance.maxHeartbeats 1600000 in

private def chartEquivL (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (hinj : Function.Injective (θ F₀ p S T hST))
    (hsurj : Function.Surjective (θ F₀ p S T hST)) :
    (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ≃ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  AlgEquiv.ofBijective (θL F₀ p S T hST) ⟨θL_injective F₀ p S T hST hinj, θL_surjective F₀ p S T hST hsurj⟩

set_option synthInstance.maxHeartbeats 1600000 in
private theorem coe_chartEquivL_one_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (hinj : Function.Injective (θ F₀ p S T hST))
    (hsurj : Function.Surjective (θ F₀ p S T hST)) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    ((chartEquivL F₀ p S T hST hinj hsurj (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b :=
  coe_θL_one_tmul F₀ p S T hST b

end TensorLeft

end CC2B01K2B
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

section

open TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve.CurveModel
open scoped TensorProduct
open CC2B01K2B

namespace CC2B01K2J

open TensorProduct

variable {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A] [Module R A]
  {L : Type*} [Field L] [Algebra ℚ L] [Module R L]

private theorem linearIndependent_rat_of_basis {V : Submodule ℤ L} {ι : Type*} (b : Module.Basis ι ℤ V) :
    LinearIndependent ℚ (fun k => (b k : L)) := by
  have h : LinearIndependent ℤ (fun k => (b k : L)) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h

private theorem injective_of_coeff (v : A →+ LaurentSeries ℚ) (hv : Function.Injective v)
    (Φ : A ⊗[R] L →+ LaurentSeries L)
    (hΦ : ∀ (a : A) (c : L) (n : ℤ),
      (Φ (a ⊗ₜ[R] c)).coeff n = c * algebraMap ℚ L ((v a).coeff n)) :
    Function.Injective Φ := by
  classical
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  refine (injective_iff_map_eq_zero Φ).mpr fun t ht => ?_
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t

  let V : Submodule ℤ L := Submodule.span ℤ (↑(s.image Prod.snd) : Set L)
  haveI : Module.Finite ℤ V := Module.Finite.span_of_finite ℤ (s.image Prod.snd).finite_toSet
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := V)
  have hli : LinearIndependent ℚ (fun k => (b k : L)) := linearIndependent_rat_of_basis b
  have hmem : ∀ i ∈ s, i.2 ∈ V := fun i hi =>
    Submodule.subset_span (by
      rw [Finset.coe_image]
      exact Set.mem_image_of_mem _ hi)

  let c' : s → V := fun i => ⟨i.1.2, hmem i.1 i.2⟩
  let a' : Fin n → A := fun k => ∑ i : s, (b.repr (c' i) k) • i.1.1
  have key : ∑ i ∈ s, i.1 ⊗ₜ[R] i.2 = ∑ k : Fin n, a' k ⊗ₜ[R] (b k : L) := by
    calc ∑ i ∈ s, i.1 ⊗ₜ[R] i.2
        = ∑ i : s, i.1.1 ⊗ₜ[R] ((c' i : V) : L) :=
          (Finset.sum_coe_sort s (fun i => i.1 ⊗ₜ[R] i.2)).symm
      _ = ∑ i : s, ∑ k : Fin n, ((b.repr (c' i) k) • i.1.1) ⊗ₜ[R] (b k : L) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (c' i)]
          rw [Submodule.coe_sum, tmul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Submodule.coe_smul, smul_tmul]
      _ = ∑ k : Fin n, ∑ i : s, ((b.repr (c' i) k) • i.1.1) ⊗ₜ[R] (b k : L) :=
          Finset.sum_comm
      _ = ∑ k : Fin n, a' k ⊗ₜ[R] (b k : L) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_tmul]
  rw [key, map_sum] at ht

  have hcoeff : ∀ (k : Fin n) (m : ℤ), (v (a' k)).coeff m = 0 := by
    intro k m
    have h0 : ∑ j : Fin n, ((v (a' j)).coeff m) • (b j : L) = 0 := by
      have h1 := congrArg (fun x : LaurentSeries L => x.coeff m) ht
      simp only [HahnSeries.coeff_sum, hΦ, HahnSeries.coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp hli _ h0 k
  have ha' : ∀ k : Fin n, a' k = 0 := fun k =>
    hv (by
      rw [map_zero]
      exact HahnSeries.coeff_inj.mp (funext fun m => by rw [hcoeff k m, HahnSeries.coeff_zero]))
  rw [key]
  exact Finset.sum_eq_zero fun k _ => by rw [ha' k, zero_tmul]

end CC2B01K2J
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

namespace CC2B01K2J

open CC2B01K2B
open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

local notation "Qb" => AlgebraicClosure ℚ

set_option synthInstance.maxHeartbeats 1600000 in

private theorem coeff_coe_θ_tmul (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) (c : Qb) (n : ℤ) :
    (((θ F₀ p S T hST (b ⊗ₜ c) : ↥(chartRing (AlgebraicClosure ℚ) T)) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
        LaurentSeries Qb).coeff n =
      c * algebraMap ℚ Qb (((b : ↥F₀) : LaurentSeries ℚ).coeff n) := by
  rw [coe_θ_tmul, Algebra.smul_def, MulMemClass.coe_mul,
    show ((algebraMap Qb (laurentBaseChange (AlgebraicClosure ℚ) F₀) c : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries Qb) =
      HahnSeries.single 0 c from algebraMap_laurentSeries_eq_single Qb c,
    HahnSeries.coeff_single_zero_mul]
  rfl

private def coeLS (S : Set ↥F₀) : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) →+ LaurentSeries ℚ :=
  AddMonoidHom.mk' (fun b => ((b : ↥F₀) : LaurentSeries ℚ)) fun _ _ => rfl

private theorem coeLS_injective (S : Set ↥F₀) :
    Function.Injective (coeLS F₀ p S) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

set_option synthInstance.maxHeartbeats 1600000 in

private def θLS (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) ⊗[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) →+ LaurentSeries Qb :=
  AddMonoidHom.mk'
    (fun t => (((θ F₀ p S T hST t : ↥(chartRing (AlgebraicClosure ℚ) T)) : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
      LaurentSeries Qb))
    fun x y => by simp only [(θ F₀ p S T hST).map_add]; rfl

set_option synthInstance.maxHeartbeats 1600000 in

private theorem θ_injective (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) : Function.Injective (θ F₀ p S T hST) := by
  have h : Function.Injective (θLS F₀ p S T hST) :=
    injective_of_coeff (coeLS F₀ p S) (coeLS_injective F₀ p S) (θLS F₀ p S T hST)
      fun b c n => coeff_coe_θ_tmul F₀ p S T hST b c n
  intro x y hxy
  exact h (congrArg (fun z : ↥(chartRing (AlgebraicClosure ℚ) T) =>
    ((z : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries Qb)) hxy)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem θFin_injective : Function.Injective (θFin F₀ j p) := θ_injective F₀ p _ _ (fin_sub F₀ j)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem θInf_injective : Function.Injective (θInf F₀ j p) := θ_injective F₀ p _ _ (inf_sub F₀ j)

end CC2B01K2J
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve.CurveModel
open scoped TensorProduct
open ModularCurve AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve.CurveModel

namespace CC2B01K2S

open scoped TensorProduct
open ModularCurve AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve.CurveModel

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem surjective_θ_of_le_span
    (S : Set ↥F₀) (T : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hST : ∀ s ∈ S, CC2B01K2B.emb F₀ s ∈ T)
    (hS7A : (chartRing (AlgebraicClosure ℚ) T).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ)
        (Set.range fun b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) => CC2B01K2B.emb F₀ (b : ↥F₀))) :
    Function.Surjective (CC2B01K2B.θ F₀ p S T hST) := by
  intro y

  have hrange :
      (Set.range fun b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) => CC2B01K2B.emb F₀ (b : ↥F₀)) =
        ⇑(chartRing (AlgebraicClosure ℚ) T).val.toLinearMap ''
          Set.range ⇑(CC2B01K2B.ρ F₀ p S T hST) := by
    rw [← Set.range_comp]; rfl
  have hy₀ : (y : (laurentBaseChange (AlgebraicClosure ℚ) F₀)) ∈
      Submodule.map (chartRing (AlgebraicClosure ℚ) T).val.toLinearMap
        (Submodule.span (AlgebraicClosure ℚ) (Set.range (CC2B01K2B.ρ F₀ p S T hST))) := by
    rw [Submodule.map_span, ← hrange]
    exact hS7A y.2
  obtain ⟨y', hy', hyy'⟩ := Submodule.mem_map.mp hy₀
  obtain rfl : y' = y := Subtype.ext hyy'
  clear hy₀ hyy' hS7A hrange

  refine Submodule.span_induction ?mem ?zero ?add ?smul hy'
  case mem =>
    rintro _ ⟨b, rfl⟩
    exact ⟨b ⊗ₜ (1 : AlgebraicClosure ℚ), by rw [CC2B01K2B.θ_tmul, map_one, mul_one]⟩
  case zero =>
    exact ⟨0, (CC2B01K2B.θ F₀ p S T hST).map_zero⟩
  case add =>
    rintro x₁ x₂ _ _ ⟨z₁, h₁⟩ ⟨z₂, h₂⟩
    exact ⟨z₁ + z₂, ((CC2B01K2B.θ F₀ p S T hST).map_add z₁ z₂).trans (by rw [h₁, h₂])⟩
  case smul =>
    rintro c x _ ⟨z, hz⟩
    refine ⟨((1 : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] c) * z, ?_⟩
    rw [(CC2B01K2B.θ F₀ p S T hST).map_mul, hz, CC2B01K2B.θ_tmul, map_one, one_mul]
    exact (Algebra.smul_def c x).symm

private theorem range_emb_eq_fin :
    (Set.range fun b : chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥F₀).2⟩ : (laurentBaseChange (AlgebraicClosure ℚ) F₀))) =
      Set.range fun b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ {j}) => CC2B01K2B.emb F₀ (b : ↥F₀) :=
  rfl

private theorem range_emb_eq_inf :
    (Set.range fun b : chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥F₀).2⟩ : (laurentBaseChange (AlgebraicClosure ℚ) F₀))) =
      Set.range fun b : ↥(chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ {j⁻¹}) => CC2B01K2B.emb F₀ (b : ↥F₀) :=
  rfl

set_option synthInstance.maxHeartbeats 1600000 in

private theorem surjective_θFin
    (hS7A : (chartRing (AlgebraicClosure ℚ)
        ({CC2B01K2B.emb F₀ j} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥F₀).2⟩ : (laurentBaseChange (AlgebraicClosure ℚ) F₀)))) :
    Function.Surjective (CC2B01K2B.θFin F₀ j p) :=
  surjective_θ_of_le_span F₀ p _ _ (CC2B01K2B.fin_sub F₀ j) (range_emb_eq_fin F₀ j p ▸ hS7A)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem surjective_θInf
    (hS7A : (chartRing (AlgebraicClosure ℚ)
        ({(CC2B01K2B.emb F₀ j)⁻¹} : Set (laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥F₀).2⟩ : (laurentBaseChange (AlgebraicClosure ℚ) F₀)))) :
    Function.Surjective (CC2B01K2B.θInf F₀ j p) :=
  surjective_θ_of_le_span F₀ p _ _ (CC2B01K2B.inf_sub F₀ j) (range_emb_eq_inf F₀ j p ▸ hS7A)

end CC2B01K2S
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ)) :
    (∃ eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))),
      ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        ((eFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ∧
    (∃ eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))),
      ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        ((eInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by
  obtain rfl : jb = CC2B01K2B.emb F₀ j := Subtype.ext hjb
  have hA := ModularCurve.chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg F₀ p j
    (CC2B01K2B.emb F₀ j) rfl
  exact ⟨⟨CC2B01K2B.chartEquivL F₀ p _ _ (CC2B01K2B.fin_sub F₀ j) (CC2B01K2J.θFin_injective F₀ j p)
      (CC2B01K2S.surjective_θFin F₀ j p hA.1),
    fun b => CC2B01K2B.coe_chartEquivL_one_tmul F₀ p _ _ (CC2B01K2B.fin_sub F₀ j) _ _ b⟩,
  ⟨CC2B01K2B.chartEquivL F₀ p _ _ (CC2B01K2B.inf_sub F₀ j) (CC2B01K2J.θInf_injective F₀ j p)
      (CC2B01K2S.surjective_θInf F₀ j p hA.2),
    fun b => CC2B01K2B.coe_chartEquivL_one_tmul F₀ p _ _ (CC2B01K2B.inf_sub F₀ j) _ _ b⟩⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange.CC2B01K2B"

end S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange (solution)
