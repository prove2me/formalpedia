-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:58.205723+00:00
-- url     : https://prove2.me/submissions/f8ce4feb-0849-47ac-b591-8598a0a82459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResDisc_isUnit_discr_of_isMaximal_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResDisc
open IsLocalRing
namespace GlobalTheory.UnitLemma.Unr.ResDisc
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (π : K.O) (π' : K'.O), algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) → IsLocalRing.maximalIdeal K.O = Ideal.span {π} → IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by
  intro K K' d φ _ π π' hππ' hm hm'
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hφ : ∀ e : K.E, φ e = algebraMap K.E K'.E e := fun _ => rfl

  have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
    intro a
    apply (hw _).2
    intro k
    obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
    refine ⟨a * c, ?_⟩
    have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
  let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
    RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
      ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
  let ι : K.O →+* K'.O :=
    e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
  have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
  letI : Algebra K.O K'.O := ι.toAlgebra
  have hsm : ∀ (a : K.O) (y : K'.O),
      algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
    intro a y
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    exact congrArg (· * _) (hι a)
  have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
      algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
    intro g v
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _

  have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
    intro k
    apply (hw _).2
    intro m
    refine ⟨if m = k then 1 else 0, ?_⟩
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  choose bv hbv using hw1
  have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
    fun y => (hw _).1 ⟨y, rfl⟩
  choose c hc using hcoord
  have hli : LinearIndependent K.O bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h1 := congrArg (algebraMap K'.O K'.E) hg
    rw [hsum, map_zero] at h1
    simp only [hbv] at h1
    have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
    exact hi (by rw [h2, map_zero])
  have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
    intro y _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c y, hj ?_⟩
    rw [hsum]
    simp only [hbv, hc]
    exact w.sum_repr _
  let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
  have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
    rw [Module.Basis.mk_apply]; exact hbv k
  have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
    intro y k
    conv_rhs => rw [← b.sum_repr y, hsum]
    simp only [hb]
    rw [w.repr_sum_self]

  have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
      Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
    intro y
    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
      map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

  have hιπ : ι π = π' := hj (by rw [hι, hππ'])
  have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hm, Ideal.map_span, Set.image_singleton]
    have h1 : algebraMap K.O K'.O π = π' := hιπ
    rw [h1, ← hm']
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨Algebra.discr K.O b, isUnit_discr_of_isMaximal_map b hmax, ?_⟩
  rw [Algebra.discr_def, RingHom.map_det]
  congr 1
  ext k m
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]
end GlobalTheory.UnitLemma.Unr.ResDisc
