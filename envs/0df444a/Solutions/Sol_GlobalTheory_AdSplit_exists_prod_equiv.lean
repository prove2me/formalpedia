-- Prove2me | solution 1 for GlobalTheory.AdSplit.exists_prod_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:18.399414+00:00
-- url     : https://prove2.me/submissions/f8edd630-a134-47ce-ab8d-62a64e87cc04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdSplit
namespace GlobalTheory.AdSplit
theorem _root_.solution (F E A B : Type) [CommRing F] [CommRing E] [Algebra F E]
    [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B] :
    letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
    letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
    letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
    ∃ e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E),
      (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z ∧
        (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) ∧
      Continuous e ∧ Continuous e.symm := by
  letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
  letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
  letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
  haveI : IsModuleTopology (A × B) ((A × B) ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology B (B ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd ((A × B) ⊗[F] E) := IsModuleTopology.toContinuousAdd (A × B) _
  haveI : ContinuousAdd (A ⊗[F] E) := IsModuleTopology.toContinuousAdd A _
  haveI : ContinuousAdd (B ⊗[F] E) := IsModuleTopology.toContinuousAdd B _
  let p := Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E)
  let q := Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E)
  let l := TensorProduct.prodLeft F F A B E
  have hl : ∀ z, l z = (p z, q z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | tmul a x => obtain ⟨a, b⟩ := a; simp [l, p, q]
    | add x y hx hy => simp [hx, hy]
  let e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E) :=
    { l.toAddEquiv with
      map_mul' := fun x y => by
        change l (x * y) = l x * l y
        simp [hl] }
  have he : ∀ z, e z = (p z, q z) := hl
  let i : A ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inl F A B)
  let j : B ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inr F A B)
  have hp : Continuous p := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.fst A B] A ⊗[F] E :=
      { toFun := p
        map_add' := map_add p
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [p, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_fst φ
  have hq : Continuous q := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.snd A B] B ⊗[F] E :=
      { toFun := q
        map_add' := map_add q
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [q, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_snd φ
  have hi : Continuous i := by
    let φ : A ⊗[F] E →ₑ+[MonoidHom.inl A B] (A × B) ⊗[F] E :=
      { toFun := i
        map_zero' := map_zero i
        map_add' := map_add i
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [i, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_id.prodMk continuous_const) φ
  have hj : Continuous j := by
    let φ : B ⊗[F] E →ₑ+[MonoidHom.inr A B] (A × B) ⊗[F] E :=
      { toFun := j
        map_zero' := map_zero j
        map_add' := map_add j
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [j, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_const.prodMk continuous_id) φ
  have hpi : ∀ x, p (i x) = x ∧ q (i x) = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [i, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  have hpj : ∀ x, p (j x) = 0 ∧ q (j x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [j, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  refine ⟨e, fun z => by rw [he]; exact ⟨rfl, rfl⟩, ?_, ?_⟩
  · have : (e : _ → _) = fun z => (p z, q z) := funext he
    rw [this]
    exact hp.prodMk hq
  · have : (e.symm : _ → _) = fun w => i w.1 + j w.2 := by
      funext w
      rw [RingEquiv.symm_apply_eq, he]
      simp [(hpi _).1, (hpi _).2, (hpj _).1, (hpj _).2]
    rw [this]
    exact (hi.comp continuous_fst).add (hj.comp continuous_snd)
end GlobalTheory.AdSplit
