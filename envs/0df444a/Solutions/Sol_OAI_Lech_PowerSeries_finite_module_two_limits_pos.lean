-- Prove2me | solution 1 for OAI.Lech.PowerSeries.finite_module_two_limits_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:02:43.987274+00:00
-- url     : https://prove2.me/submissions/a2c9bb6c-9452-4a08-81c8-5ca8cf47144d

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L016
import Theorems.Thm_OAI_Lech_PowerSeries_maximal_power_colength

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex

open scoped BigOperators
namespace Lech

variable {R : Type*} [CommRing R]

 
lemma sup_pow_add_pred_le (I J : Ideal R) (n m : ℕ) :
    (I ⊔ J) ^ (n + m - 1) ≤ I ^ n ⊔ J ^ m := by
  rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left))
  · refine Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right))
    omega

 
lemma finset_sup_pow_le {ι : Type*} (s : Finset ι) (I : ι → Ideal R)
    (a : ℕ) (ha : 1 ≤ a) :
    s.sup I ^ (s.card * (a - 1) + 1) ≤ s.sup (fun j => I j ^ a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj hs =>
    rw [Finset.sup_insert, Finset.sup_insert, Finset.card_insert_of_notMem hj]
    have he : (s.card + 1) * (a - 1) + 1 = a + (s.card * (a - 1) + 1) - 1 := by
      rw [add_mul, one_mul]
      omega
    rw [he]
    exact (sup_pow_add_pred_le (I j) (s.sup I) a _).trans (sup_le_sup_left hs _)

 

lemma parameter_power_cofinality (h a : ℕ) (ha : 1 ≤ a) (z : Fin h → R) :
    (Ideal.span (Set.range z)) ^ (h * (a - 1) + 1) ≤
      Ideal.span (Set.range fun j => z j ^ a) ∧
    Ideal.span (Set.range fun j => z j ^ a) ≤ (Ideal.span (Set.range z)) ^ a := by
  constructor
  · have H := finset_sup_pow_le Finset.univ (fun j : Fin h => Ideal.span {z j}) a ha
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.sup_univ_eq_iSup,
      Ideal.span_singleton_pow, ← Ideal.span_range_eq_iSup] using H
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) a

end Lech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFiniteFree
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech

 

theorem finite_free_factorization (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (g : A), g ≠ 0 ∧
      ∃ (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A)),
        u.comp v = g • LinearMap.id ∧ v.comp u = g • LinearMap.id := by
  let := Module.finitePresentation_of_finite A M
  let K := FractionRing A
  let MK := LocalizedModule A⁰ M
  let f : M →ₗ[A] MK := LocalizedModule.mkLinearMap A⁰ M
  let n := Module.finrank K MK
  let e : MK ≃ₗ[A] (Fin n → K) := (Module.finBasis K MK).equivFun.restrictScalars A
  let j : (Fin n → A) →ₗ[A] (Fin n → K) :=
    LinearMap.pi fun i => (Algebra.linearMap A K).comp (LinearMap.proj i)
  have : IsLocalizedModule A⁰ j := by dsimp [j]; infer_instance
  obtain ⟨v,s,hv⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ j
    (e.toLinearMap.comp f)
  obtain ⟨u,t,hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ f
    (e.symm.toLinearMap.comp j)
  have huv : f.comp (u.comp v) = f.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu (v x)
    have hs := LinearMap.congr_fun hv x
    change f (u (v x)) = (t:A) • e.symm (j (v x)) at ht
    change j (v x) = (s:A) • e (f x) at hs
    change f (u (v x)) = f (((t:A)*(s:A)) • x)
    rw [ht,hs,map_smul,e.symm_apply_apply,map_smul,mul_smul]
  have hvu : j.comp (v.comp u) = j.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu x
    have hs := LinearMap.congr_fun hv (u x)
    change f (u x) = (t:A) • e.symm (j x) at ht
    change j (v (u x)) = (s:A) • e (f (u x)) at hs
    change j (v (u x)) = j (((t:A)*(s:A)) • x)
    rw [hs,ht,map_smul,e.apply_symm_apply,map_smul,mul_smul,smul_comm]
  obtain ⟨a,ha⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ f
    (u.comp v) (((t:A)*(s:A)) • LinearMap.id) huv
  obtain ⟨b,hb⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ j
    (v.comp u) (((t:A)*(s:A)) • LinearMap.id) hvu
  refine ⟨n,(a:A)*(b:A)*((t:A)*(s:A)),?_, ((a:A)*(b:A)) • u,v,?_,?_⟩
  · exact mul_ne_zero (mul_ne_zero (nonZeroDivisors.coe_ne_zero a)
      (nonZeroDivisors.coe_ne_zero b))
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero t) (nonZeroDivisors.coe_ne_zero s))
  · rw [LinearMap.smul_comp, mul_comm (a:A) (b:A),mul_smul]
    change (b:A) • ((a:A) • u.comp v) = _
    rw [show (a:A) • u.comp v = (a:A) • (((t:A)*(s:A)) • LinearMap.id) from ha]
    simp only [smul_smul]
    congr 1
    ring
  · rw [LinearMap.comp_smul,mul_smul]
    change (a:A) • ((b:A) • v.comp u) = _
    rw [show (b:A) • v.comp u = (b:A) • (((t:A)*(s:A)) • LinearMap.id) from hb]
    simp only [smul_smul]
    congr 1
    ring

variable {A M N P : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

 

lemma length_kernel_eq_cokernel (f : M →ₗ[A] M) (hM : Module.length A M ≠ ⊤) :
    Module.length A f.ker = Module.length A (M ⧸ f.range) := by
  have h₁ := Module.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hk] at h₁
  have h₂ := Module.length_eq_add_of_exact f.range.subtype f.range.mkQ
    (Submodule.subtype_injective _) f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  have hr : Module.length A f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective f.range.subtype
      (Submodule.subtype_injective _))
  exact WithTop.add_left_cancel hr ((add_comm _ _).trans (h₁.symm.trans h₂))

 

lemma length_torsion_subquotient_le (i : N →ₗ[A] M) (q : N →ₗ[A] P)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (g : A) (hg : ∀ x : P, g • x = 0) (hM : Module.length A M ≠ ⊤) :
    Module.length A P ≤ Module.length A (M ⧸ (LinearMap.lsmul A M g).range) := by
  let fN := LinearMap.lsmul A N g
  let fM := LinearMap.lsmul A M g
  have hqker : fN.range ≤ q.ker := by
    rintro x ⟨y,rfl⟩
    change q (g • y) = 0
    rw [map_smul,hg]
  let q' := fN.range.liftQ q hqker
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨fN.range.mkQ y,rfl⟩
  let i' : fN.ker →ₗ[A] fM.ker :=
    (i.comp fN.ker.subtype).codRestrict fM.ker (by
      intro x
      change g • i x = 0
      rw [← map_smul]
      simpa only [fN, LinearMap.lsmul_apply, map_zero] using congrArg i x.property)
  have hi' : Function.Injective i' := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  have hN : Module.length A N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective i hi)
  calc
    Module.length A P ≤ Module.length A (N ⧸ fN.range) :=
      Module.length_le_of_surjective q' hq'
    _ = Module.length A fN.ker := (length_kernel_eq_cokernel fN hN).symm
    _ ≤ Module.length A fM.ker := Module.length_le_of_injective i' hi'
    _ = _ := length_kernel_eq_cokernel fM hM

lemma length_scalar_cokernel_pi (g : A) (n : ℕ) :
    Module.length A ((Fin n → A) ⧸ (LinearMap.lsmul A (Fin n → A) g).range) =
      n * Module.length A (A ⧸ (LinearMap.lsmul A A g).range) := by
  classical
  have he : (LinearMap.lsmul A (Fin n → A) g).range =
      Submodule.pi Set.univ (fun _ : Fin n => (LinearMap.lsmul A A g).range) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩ i _
      exact ⟨y i,rfl⟩
    · intro hx
      have hx' : ∀ i, ∃ y : A, g • y = x i := fun i => hx i (Set.mem_univ i)
      choose y hy using hx'
      exact ⟨y,funext hy⟩
  rw [(Submodule.quotEquivOfEq _ _ he).length_eq,
    (Submodule.quotientPi (fun _ : Fin n => (LinearMap.lsmul A A g).range)).length_eq,
    Module.length_pi_of_fintype]
  simp

 

lemma length_isogeny (n c : ℕ) (g : A)
    (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A))
    (huv : u.comp v = g • LinearMap.id)
    (hvu : v.comp u = g • LinearMap.id)
    (w : (Fin c → A) →ₗ[A] M) (hw : Function.Surjective w)
    (hA : Module.length A A ≠ ⊤) :
    Module.length A M ≤ n * Module.length A A +
        c * Module.length A (A ⧸ (LinearMap.lsmul A A g).range) ∧
    n * Module.length A A ≤ Module.length A M +
        n * Module.length A (A ⧸ (LinearMap.lsmul A A g).range) := by
  have hfree (d : ℕ) : Module.length A (Fin d → A) = d * Module.length A A := by
    simp
  have hfin (d : ℕ) : Module.length A (Fin d → A) ≠ ⊤ := by
    rw [hfree]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top d) hA
  have hker : ∀ x : u.ker, g • x = 0 := by
    intro x
    apply Subtype.ext
    have hh := LinearMap.congr_fun hvu x
    simpa using hh.symm
  have hcoker : ∀ x : M ⧸ u.range, g • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change u.range.mkQ (g • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨v x,LinearMap.congr_fun huv x⟩
  have hk := length_torsion_subquotient_le u.ker.subtype LinearMap.id
    (Submodule.subtype_injective _) Function.surjective_id g hker (hfin n)
  rw [length_scalar_cokernel_pi] at hk
  let wc := u.range.mkQ.comp w
  have hwc : Function.Surjective wc := u.range.mkQ_surjective.comp hw
  have hc := length_torsion_subquotient_le LinearMap.id wc
    Function.injective_id hwc g hcoker (hfin c)
  rw [length_scalar_cokernel_pi] at hc
  have hr := Module.length_le_of_surjective u.rangeRestrict u.surjective_rangeRestrict
  have hr' := Module.length_le_of_injective u.range.subtype (Submodule.subtype_injective _)
  have hcod := Module.length_eq_add_of_exact u.range.subtype u.range.mkQ
    (Submodule.subtype_injective _) u.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ u.range)
  have hdom := Module.length_eq_add_of_exact u.rangeRestrict.ker.subtype u.rangeRestrict
    (Submodule.subtype_injective _) u.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map u.rangeRestrict)
  have hkr : u.rangeRestrict.ker = u.ker := by ext x; simp
  rw [hkr,hfree] at hdom
  constructor
  · rw [hcod]
    exact add_le_add (by simpa only [hfree] using hr) hc
  · rw [hdom,add_comm]
    exact add_le_add hr' hk

lemma scalar_range (a : A) : (LinearMap.lsmul A A a).range = Ideal.span {a} := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, smul_eq_mul,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨y,hy⟩ => ⟨y,by simpa [mul_comm] using hy.symm⟩,
    fun ⟨y,hy⟩ => ⟨y,by simpa [mul_comm] using hy.symm⟩⟩

lemma scalar_cokernel_quotient_length (I : Ideal A) (g : A) :
    Module.length (A ⧸ I)
      ((A ⧸ I) ⧸ (LinearMap.lsmul (A ⧸ I) (A ⧸ I) (Ideal.Quotient.mk I g)).range) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  rw [scalar_range]
  have hm : Ideal.span {Ideal.Quotient.mk I g} =
      (Ideal.span {g}).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hm, ← Module.length_eq_of_surjective (R := A ⧸ I)
    (Ideal.Quotient.mk_surjective)]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A I (Ideal.span {g})).toLinearEquiv.length_eq

lemma baseChange_isogeny {B : Type*} [CommRing B] [Algebra A B]
    (n : ℕ) (g : A) (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A))
    (huv : u.comp v = g • LinearMap.id) (hvu : v.comp u = g • LinearMap.id) :
    ∃ (u' : (Fin n → B) →ₗ[B] B ⊗[A] M) (v' : B ⊗[A] M →ₗ[B] (Fin n → B)),
      u'.comp v' = (algebraMap A B g) • LinearMap.id ∧
      v'.comp u' = (algebraMap A B g) • LinearMap.id := by
  let e := TensorProduct.piScalarRight A B B (Fin n)
  refine ⟨(u.baseChange B).comp e.symm.toLinearMap,
    e.toLinearMap.comp (v.baseChange B),?_,?_⟩
  · apply LinearMap.ext
    intro x
    change u.baseChange B (e.symm (e (v.baseChange B x))) = _
    rw [e.symm_apply_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      huv, LinearMap.baseChange_smul, LinearMap.baseChange_id]
    simp [Algebra.smul_def]
  · apply LinearMap.ext
    intro x
    change e (v.baseChange B (u.baseChange B (e.symm x))) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      hvu, LinearMap.baseChange_smul, LinearMap.baseChange_id]
    change e (g • e.symm x) = (algebraMap A B g) • x
    rw [← IsScalarTower.algebraMap_smul B g (e.symm x), map_smul, e.apply_symm_apply]



end Lech


namespace Lech
open Filter
open scoped Topology

lemma tendsto_of_abs_sub_le {f g ε : ℕ → ℝ} {a : ℝ}
    (hg : Tendsto g atTop (𝓝 a)) (he : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, |f n - g n| ≤ ε n) : Tendsto f atTop (𝓝 a) := by
  have hz : Tendsto (fun n => |f n - g n|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) h he
  have hs : Tendsto (fun n => f n - g n) atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [Real.dist_eq,sub_zero] using hz
  simpa only [sub_add_cancel,zero_add] using hs.add hg



end Lech


namespace Lech
open scoped TensorProduct
theorem finite_module_colength_compare_pos (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ (n c : ℕ) (g : A), 0 < n ∧ g ≠ 0 ∧ ∀ (I : Ideal A),
      Module.length A (A ⧸ I) ≠ ⊤ →
      Module.length A (M ⧸ (I • (⊤ : Submodule A M))) ≤
        n * Module.length A (A ⧸ I) + c * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) ∧
      n * Module.length A (A ⧸ I) ≤
        Module.length A (M ⧸ (I • (⊤ : Submodule A M))) +
        n * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  obtain ⟨n,g,hg,u,v,huv,hvu⟩ := finite_free_factorization A M
  obtain ⟨c,w,hw⟩ := Module.Finite.exists_fin' A M
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    apply hfaithful g hg
    rw [← huv]
    ext x
    change u (v x) = 0
    rw [Subsingleton.elim (v x) 0,map_zero]
  refine ⟨n,c,g,hn,hg,fun I hI => ?_⟩
  let B := A ⧸ I
  obtain ⟨u',v',huv',hvu'⟩ := baseChange_isogeny (B := B) n g u v huv hvu
  let e := TensorProduct.piScalarRight A B B (Fin c)
  let w' := (w.baseChange B).comp e.symm.toLinearMap
  have hw' : Function.Surjective w' := (LinearMap.baseChange_surjective B hw).comp e.symm.surjective
  have hB : Module.length B B ≠ ⊤ := by
    rwa [← Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
  have h := length_isogeny n c (algebraMap A B g) u' v' huv' hvu' w' hw' hB
  have hlen : Module.length B (B ⊗[A] M) = Module.length A (M ⧸ I • (⊤ : Submodule A M)) := by
    rw [← Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
    exact (TensorProduct.quotTensorEquivQuotSMul M I).length_eq
  have hscalar : Module.length B
      (B ⧸ (LinearMap.lsmul B B (algebraMap A B g)).range) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {g})) :=
    scalar_cokernel_quotient_length I g
  rw [hlen, hscalar, ← Module.length_eq_of_surjective (R := B)
    Ideal.Quotient.mk_surjective] at h
  exact h

end Lech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped nonZeroDivisors
variable (k : Type*) [Field k]

lemma fin_le_dimension (h : ℕ) : (h : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin h) k) := by
  induction h with
  | zero => exact Order.krullDim_nonneg
  | succ h ih =>
    let e : Fin h ↪ Fin (h+1) := Fin.succEmb h
    let f := (killCompl (R := k) e).toRingHom
    have hf : Function.Surjective f := fun x => ⟨rename e x,killCompl_rename_app x⟩
    have hx : (X 0 : MvPowerSeries (Fin (h+1)) k) ∈ (MvPowerSeries (Fin (h+1)) k)⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hz
        have hc := congrArg (coeff (Finsupp.single 0 1)) hz
        simp at hc)
    have hz : f (X 0) = 0 := by
      apply killCompl_X_eq_zero
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    have hb := ringKrullDim_succ_le_of_surjective f hf hx hz
    calc
      (↑(h+1) : WithBot ℕ∞) = (h : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (MvPowerSeries (Fin h) k) + 1 := add_le_add ih le_rfl
      _ ≤ _ := hb

lemma fin_dimension (h : ℕ) : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
  apply le_antisymm _ (fin_le_dimension k h)
  simpa using dimension_le_variables (Fin h) k

end Lech.PowerSeries


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))

 

theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top

 
theorem colength_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    (colength A N : ℕ∞) = Module.length A (A ⧸ (IsLocalRing.maximalIdeal A)^N) :=
  ENat.natCast_toNat (quotient_length_ne_top A N)

end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
namespace Lech

lemma length_le_add_of_exact {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hg : Function.Surjective g)
    (he : Function.Exact f g) :
    Module.length R M ≤ Module.length R N + Module.length R P := by
  let f' : N →ₗ[R] g.ker := f.codRestrict g.ker (fun n => by
    rw [LinearMap.exact_iff.mp he]
    exact ⟨n, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨m, hm⟩
    rw [LinearMap.exact_iff.mp he] at hm
    obtain ⟨n, rfl⟩ := hm
    exact ⟨n, rfl⟩
  rw [Module.length_eq_add_of_exact g.ker.subtype g g.ker.subtype_injective hg
    (LinearMap.exact_subtype_ker_map g)]
  exact add_le_add (Module.length_le_of_surjective f' hf') le_rfl

namespace ParameterBound
variable {R : Type*} [CommRing R]

lemma length_mul_le (J : Ideal R) (x y : R) :
    Module.length R (R ⧸ (J ⊔ Ideal.span {x * y})) ≤
      Module.length R (R ⧸ (J ⊔ Ideal.span {x})) +
        Module.length R (R ⧸ (J ⊔ Ideal.span {y})) := by
  let A := J ⊔ Ideal.span {x}
  let B := J ⊔ Ideal.span {x * y}
  let C := J ⊔ Ideal.span {y}
  have hmul : ∀ z ∈ A, y * z ∈ B := by
    intro z hz
    obtain ⟨j, hj, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [mul_add]
    apply B.add_mem
    · exact Submodule.mem_sup_left (J.mul_mem_left y hj)
    · apply Submodule.mem_sup_right
      apply Ideal.mem_span_singleton'.mpr
      exact ⟨a, by ring⟩
  let f : (R ⧸ A) →ₗ[R] R ⧸ B :=
    A.liftQ (B.mkQ.comp (LinearMap.lsmul R R y)) (by
      intro z hz
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hmul z hz))
  have hBC : B ≤ C := by
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩)
  let g : (R ⧸ B) →ₗ[R] R ⧸ C := B.mapQ C LinearMap.id hBC
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨r, rfl⟩ := C.mkQ_surjective q
    exact ⟨B.mkQ r, rfl⟩
  apply length_le_add_of_exact f g hg
  rw [LinearMap.exact_iff]
  ext q
  obtain ⟨r, rfl⟩ := B.mkQ_surjective q
  constructor
  · intro hr
    change C.mkQ r = 0 at hr
    have hrC := (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨j, hj, t, ht, he⟩ := Submodule.mem_sup.mp hrC
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    refine ⟨A.mkQ a, ?_⟩
    change B.mkQ (y * a) = B.mkQ r
    apply (Submodule.Quotient.eq _).mpr
    rw [← he]
    have he' : y * a - (j + a * y) = -j := by ring
    rw [he']
    exact B.neg_mem (Submodule.mem_sup_left hj)
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := A.mkQ_surjective a
    change B.mkQ (y * a) = B.mkQ r at ha
    change g (B.mkQ r) = 0
    rw [← ha]
    change C.mkQ (y * a) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, mul_comm _ _⟩)

lemma length_pow_le (J : Ideal R) (x : R) (n : ℕ) :
    Module.length R (R ⧸ (J ⊔ Ideal.span {x ^ n})) ≤
      n * Module.length R (R ⧸ (J ⊔ Ideal.span {x})) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (length_mul_le J (x ^ n) x).trans (add_le_add ih le_rfl)

lemma length_parameter_powers_le (n : ℕ) (x : Fin n → R) (J : Ideal R) (N : ℕ) :
    Module.length R (R ⧸ (J ⊔ Ideal.span (Set.range (fun i => x i ^ N)))) ≤
      (N : ℕ∞) ^ n * Module.length R (R ⧸ (J ⊔ Ideal.span (Set.range x))) := by
  induction n generalizing J with
  | zero =>
      have he : (fun i : Fin 0 => x i ^ N) = x := funext (fun i => Fin.elim0 i)
      rw [he, pow_zero, one_mul]
  | succ n ih =>
      rw [Fin.range_fin_succ, Ideal.span_insert, Fin.range_fin_succ, Ideal.span_insert]
      have h1 := length_pow_le (J ⊔ Ideal.span (Set.range (fun i : Fin n => x i.succ ^ N)))
         (x 0) N
      have h2 := ih (fun i => x i.succ) (J ⊔ Ideal.span {x 0})
      have h2' := mul_le_mul_right h2 (N : ℕ∞)
      rw [sup_right_comm J] at h2'
      have h := h1.trans h2'
      change Module.length R (R ⧸ (J ⊔ (Ideal.span {x 0 ^ N} ⊔
        Ideal.span (Set.range (fun i : Fin n => x i.succ ^ N))))) ≤
        (N : ℕ∞) ^ (n + 1) * Module.length R (R ⧸ (J ⊔
          (Ideal.span {x 0} ⊔ Ideal.span (Set.range (fun i : Fin n => x i.succ)))))
      rw [← sup_assoc, sup_right_comm J, ← sup_assoc, pow_succ', mul_assoc]
      exact h

end ParameterBound
end Lech


namespace Lech
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

lemma colength_polynomial_bound :
    ∃ C : ℕ, ∀ N : ℕ, colength R N ≤ N ^ dimension R * C := by
  classical
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨s, hp, hc⟩ := m.exists_finset_card_eq_height_of_isNoetherianRing
  let I := Ideal.span (s : Set R)
  let x : Fin s.card → R := fun i => ((s.equivFin).symm i).val
  have hx : Set.range x = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact ((s.equivFin).symm i).property
    · intro hr
      exact ⟨s.equivFin ⟨r, hr⟩, congrArg Subtype.val ((s.equivFin).symm_apply_apply _)⟩
  have hxm (i : Fin s.card) : x i ∈ m :=
    hp.le (Ideal.subset_span (by rw [← hx]; exact Set.mem_range_self i))
  have hcard : s.card = dimension R := by
    have h := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hc
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← dimension_cast R] at h
    exact Nat.cast_injective (WithBot.coe_injective h)
  let : IsArtinianRing (R ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
  have hfinite : Module.length R (R ⧸ I) ≠ ⊤ := by
    rw [Module.length_eq_of_surjective (R := R ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top
  let C := (Module.length R (R ⧸ I)).toNat
  have hC : (C : ℕ∞) = Module.length R (R ⧸ I) := ENat.natCast_toNat hfinite
  refine ⟨C, fun N => ?_⟩
  have hpow : Ideal.span (Set.range (fun i => x i ^ N)) ≤ m ^ N := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_pow (hxm i) N
  have h1 := length_quotient_le R hpow
  have h2 := ParameterBound.length_parameter_powers_le s.card x (⊥ : Ideal R) N
  rw [bot_sup_eq, bot_sup_eq, hx] at h2
  have h := h1.trans h2
  rw [hcard, ← hC, ← Nat.cast_pow, ← Nat.cast_mul] at h
  rw [← colength_cast R] at h
  exact ENat.natCast_le_natCast.mp h
end Lech

open scoped BigOperators


namespace Lech.FrobeniusGrowth
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R]


lemma pow_mem_powerIdeal (H : Ideal R) (q : ℕ) {x : R} (hx : x ∈ H) :
    x^q ∈ powerIdeal H q := Ideal.subset_span ⟨x,hx,rfl⟩

lemma pigeonhole (H : Ideal R) (hH : H.FG) :
    ∃ t : ℕ, ∀ q : ℕ, 1 ≤ q → H^(t*(q-1)+1) ≤ powerIdeal H q := by
  classical
  obtain ⟨s,hs⟩ := hH
  let z : Fin s.card → R := fun i => ((s.equivFin).symm i).val
  have hz : Set.range z = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i,rfl⟩
      exact ((s.equivFin).symm i).property
    · intro hr
      exact ⟨s.equivFin ⟨r,hr⟩,congrArg Subtype.val ((s.equivFin).symm_apply_apply _)⟩
  refine ⟨s.card,fun q hq => ?_⟩
  have h := (Lech.parameter_power_cofinality s.card q hq z).1
  rw [hz,hs] at h
  refine h.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i,rfl⟩
  apply pow_mem_powerIdeal
  rw [← hs]
  exact Ideal.subset_span (by rw [← hz]; exact Set.mem_range_self i)

lemma linear_power_containment [IsNoetherianRing R] [IsLocalRing R]
    (H : Ideal R) (hH : H.radical = IsLocalRing.maximalIdeal R) :
    ∃ c : ℕ, ∀ q : ℕ, 1 ≤ q → (IsLocalRing.maximalIdeal R)^(c*q) ≤ powerIdeal H q := by
  obtain ⟨a,ha⟩ := H.exists_radical_pow_le_of_fg H.radical.fg_of_isNoetherianRing
  rw [hH] at ha
  obtain ⟨t,ht⟩ := pigeonhole H H.fg_of_isNoetherianRing
  refine ⟨a*(t+1),fun q hq => ?_⟩
  have he : t*(q-1)+1 ≤ (t+1)*q := by
    calc
      _ ≤ t*q+q := Nat.add_le_add (Nat.mul_le_mul_left t (Nat.sub_le q 1)) hq
      _ = _ := by ring
  calc
    _ = ((IsLocalRing.maximalIdeal R)^a)^((t+1)*q) := by rw [← pow_mul]; congr 1; ring
    _ ≤ H^((t+1)*q) := pow_le_pow_left' ha _
    _ ≤ H^(t*(q-1)+1) := Ideal.pow_le_pow_right he
    _ ≤ powerIdeal H q := ht q hq

lemma quotient_power_length (I J : Ideal R) (n : ℕ) :
    Module.length (R ⧸ J) ((R ⧸ J) ⧸ (I.map (Ideal.Quotient.mk J)) ^ n) =
      Module.length R (R ⧸ (I ^ n ⊔ J)) := by
  rw [← Ideal.map_pow]
  have he := (DoubleQuot.quotQuotEquivQuotSupₐ R J (I ^ n)).toLinearEquiv.length_eq
  rw [sup_comm] at he
  have hlen := Module.length_eq_of_surjective (S := R) (R := R ⧸ J)
    (M := (R ⧸ J) ⧸ (I ^ n).map (Ideal.Quotient.mk J))
    (Ideal.Quotient.mk_surjective (I := J))
  exact hlen.symm.trans he

variable [IsNoetherianRing R] [IsLocalRing R]

lemma quotient_dimension_lt {g : R} (hg : g ∈ R⁰) [IsLocalRing (R ⧸ Ideal.span {g})] :
    Lech.dimension (R ⧸ Ideal.span {g}) < Lech.dimension R := by
  have hh := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hg
  rw [← Lech.dimension_cast (R ⧸ Ideal.span {g}),← Lech.dimension_cast R] at hh
  have hh' : (Lech.dimension (R ⧸ Ideal.span {g}) : WithBot ℕ∞) +
      (1 : WithBot ℕ∞) ≤ (Lech.dimension R : WithBot ℕ∞) := hh
  exact_mod_cast hh'

lemma quotient_colength_bound (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q →
      Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≤
        (C : ℕ∞) * (q : ℕ∞)^(Lech.dimension R - 1) := by
  by_cases hu : IsUnit g
  · refine ⟨0,fun q hq => ?_⟩
    simp [Ideal.span_singleton_eq_top.mpr hu]
  have hJ : Ideal.span ({g} : Set R) ≠ ⊤ := fun hh => hu (Ideal.span_singleton_eq_top.mp hh)
  let B := R ⧸ Ideal.span {g}
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hm : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {g})) =
      IsLocalRing.maximalIdeal B := by
    apply IsLocalRing.eq_maximalIdeal
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact IsLocalRing.le_maximalIdeal hJ
  obtain ⟨c,hc⟩ := linear_power_containment H hH
  obtain ⟨C,hC⟩ := Lech.colength_polynomial_bound B
  refine ⟨c^(Lech.dimension B)*C,fun q hq => ?_⟩
  have hh := Lech.length_quotient_le R
    (sup_le_sup_right (hc q hq) (Ideal.span {g}))
  rw [← quotient_power_length,hm,← Lech.colength_cast B] at hh
  have hdim : Lech.dimension B ≤ Lech.dimension R - 1 := by
    have hh := quotient_dimension_lt hg
    change Lech.dimension B < Lech.dimension R at hh
    omega
  have hn := (hC (c*q)).trans (show (c*q)^Lech.dimension B*C ≤
      (c^Lech.dimension B*C)*q^(Lech.dimension R-1) from by
    rw [mul_pow,mul_right_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq hdim))
  exact hh.trans (by exact_mod_cast hn)

open Filter
open scoped Topology

 
theorem normalized_error_bound (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q →
      ((Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R ≤ (C : ℝ) / q := by
  obtain ⟨C,hC⟩ := quotient_colength_bound H hH hg
  by_cases hd : Lech.dimension R = 0
  · have hu : IsUnit g := by
      by_contra hu
      have hJ : Ideal.span ({g} : Set R) ≠ ⊤ := fun hh => hu (Ideal.span_singleton_eq_top.mp hh)
      have : Nontrivial (R ⧸ Ideal.span {g}) := Ideal.Quotient.nontrivial_iff.mpr hJ
      have : IsLocalRing (R ⧸ Ideal.span {g}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have := quotient_dimension_lt hg
      omega
    exact ⟨0,fun q hq => by simp [Ideal.span_singleton_eq_top.mpr hu]⟩
  refine ⟨C,fun q hq => ?_⟩
  have hb := hC q hq
  have hf : Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [← Nat.cast_pow,← Nat.cast_mul]; exact ENat.natCast_ne_top _) hb
  rw [← ENat.natCast_toNat hf,← Nat.cast_pow,← Nat.cast_mul] at hb
  have hb' : ((Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toNat : ℝ) ≤
      (C : ℝ)*(q : ℝ)^(Lech.dimension R-1) := by exact_mod_cast hb
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ ((C : ℝ)*(q : ℝ)^(Lech.dimension R-1))/(q : ℝ)^Lech.dimension R :=
      div_le_div_of_nonneg_right hb' (by positivity)
    _ = (C : ℝ)/q := by
      rw [show Lech.dimension R = (Lech.dimension R-1)+1 from by omega,
        pow_succ]
      field_simp
      simp only [Nat.add_sub_cancel]

theorem normalized_error_tendsto (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := normalized_error_bound H hH hg
  apply squeeze_zero' (Eventually.of_forall (fun q => by positivity))
    ((eventually_ge_atTop 1).mono (fun q hq => hC q hq))
  simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
    Tendsto (fun q : ℕ => (C : ℝ)/(q : ℝ)) atTop (𝓝 0))

end Lech.FrobeniusGrowth


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.FrobeniusGrowth
open Filter
open scoped Topology nonZeroDivisors
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma powerIdeal_le_pow (H : Ideal R) (q : ℕ) : powerIdeal H q ≤ H^q := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  exact Ideal.pow_mem_pow hx q

lemma ordinary_error_tendsto (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (H^q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := quotient_colength_bound H hH hg
  apply squeeze_zero' (Eventually.of_forall (fun q => by positivity))
    ((eventually_ge_atTop 1).mono (fun q hq => ?_))
    (normalized_error_tendsto H hH hg)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb := Lech.length_quotient_le R (sup_le_sup_right (powerIdeal_le_pow H q) (Ideal.span {g}))
  have hf : Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [← Nat.cast_pow,← Nat.cast_mul]; exact ENat.natCast_ne_top _) (hC q hq)
  exact_mod_cast ENat.toNat_le_toNat hb hf

end Lech.FrobeniusGrowth


namespace Lech.FrobeniusGrowth
open Filter IsLocalRing
open scoped Topology nonZeroDivisors
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma normalized_error_of_linear_containment (J : ℕ → Ideal R)
    (b : ℕ) (hb : 0 < b) (hJ : ∀ q, 1 ≤ q → (maximalIdeal R)^(b*q) ≤ J q)
    {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (J q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
  have hmul : Tendsto (fun q : ℕ => b*q) atTop atTop :=
    tendsto_atTop_mono (fun q => Nat.le_mul_of_pos_left q hb) tendsto_id
  have ht := (ordinary_error_tendsto (maximalIdeal R) (Ideal.IsPrime.radical inferInstance) hg).comp hmul
  have ht' : Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ ((maximalIdeal R)^(b*q) ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
    have h := ht.const_mul ((b : ℝ)^Lech.dimension R)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with q hq
    dsimp only [Function.comp_apply]
    rw [Nat.cast_mul,mul_pow]
    field_simp
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity))
    ((eventually_ge_atTop 1).mono (fun q hq => ?_)) ht'
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hl := Lech.length_quotient_le R (sup_le_sup_right (hJ q hq) (Ideal.span {g}))
  have hf : Module.length R (R ⧸ ((maximalIdeal R)^(b*q) ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (b*q))
      (Lech.length_quotient_le R le_sup_left)
  exact_mod_cast ENat.toNat_le_toNat hl hf

omit [IsNoetherianRing R] in
lemma parameter_power_linear_containment (h : ℕ) (hh : 0 < h) (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) (q : ℕ) (hq : 1 ≤ q) :
    (maximalIdeal R)^(h*q) ≤ Ideal.span (Set.range fun i => z i^q) := by
  have he : h*(q-1)+1 ≤ h*q := by
    calc
      _ ≤ h*(q-1)+h := Nat.add_le_add_left hh _
      _ = h*q := by rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
  rw [← hz]
  exact (Ideal.pow_le_pow_right he).trans (Lech.parameter_power_cofinality h q hq z).1

lemma parameter_error_tendsto (h : ℕ) (hh : 0 < h) (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (Ideal.span (Set.range fun i => z i^q) ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) :=
  normalized_error_of_linear_containment _ h hh (parameter_power_linear_containment h hh z hz) hg

end Lech.FrobeniusGrowth


open CategoryTheory


namespace Lech.RootTower
open MvPowerSeries IsLocalRing
variable {σ k : Type*} [Fintype σ] [Field k] (q : ℕ) [NeZero q]

omit [Fintype σ] in
lemma expansion_residue_surjective : Function.Surjective
    (ResidueField.map (algebraMap (MvPowerSeries σ k) (Expanded (σ := σ) (R := k) q))) := by
  intro x
  obtain ⟨f,rfl⟩ := residue_surjective x
  refine ⟨residue (MvPowerSeries σ k) (C (constantCoeff f)), ?_⟩
  rw [ResidueField.map_residue]
  change residue (MvPowerSeries σ k) (expand q (NeZero.ne q) (C (constantCoeff f))) = _
  rw [expand_C]
  exact (residue_eq_constant f).symm

lemma variable_powers_colength :
    Module.length (MvPowerSeries σ k)
      (MvPowerSeries σ k ⧸ Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ k)^q))) =
      (q ^ Fintype.card σ : ℕ) := by
  have hid : (maximalIdeal (MvPowerSeries σ k)).map
      (expand (σ := σ) (R := k) q (NeZero.ne q)).toRingHom =
      Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ k)^q)) := by
    rw [Lech.PowerSeries.maximalIdeal_eq_variables, Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact MvPowerSeries.expand_X q (NeZero.ne q) i
  have h := fiber_length_of_basis (expansionBasis (σ := σ) (R := k) q)
    (expansion_residue_surjective (σ := σ) (k := k) q)
  change Module.length (MvPowerSeries σ k) (MvPowerSeries σ k ⧸
    (maximalIdeal (MvPowerSeries σ k)).map
      (expand q (NeZero.ne q)).toRingHom) = _ at h
  rw [hid] at h
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

end Lech.RootTower


namespace Lech
open Filter
open scoped Topology

lemma ascFactorial_normalized_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n.ascFactorial h : ℝ) / (n : ℝ)^h) atTop (𝓝 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + h)/(n : ℝ)) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => (h : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hh := hc.const_add 1
      apply (show Tendsto (fun n : ℕ => 1 + (h : ℝ)/(n : ℝ)) atTop (𝓝 1) from by
        simpa only [add_zero] using hh).congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [add_div,div_self (by exact_mod_cast hn.ne')]
    convert ht.mul ih using 1
    · funext n
      rw [Nat.ascFactorial_succ,Nat.cast_mul,Nat.cast_add,pow_succ]
      ring
    · simp

lemma binomial_normalized_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (h.factorial : ℝ) * ((n+h-1).choose h : ℝ) /
      (n : ℝ)^h) atTop (𝓝 1) := by
  simpa only [Nat.ascFactorial_eq_factorial_mul_choose',Nat.cast_mul] using
    ascFactorial_normalized_tendsto h

end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology nonZeroDivisors
variable {k : Type*} [Field k]

lemma fin_dimension_nat (h : ℕ) : Lech.dimension (MvPowerSeries (Fin h) k) = h := by
  simp [Lech.dimension,fin_dimension]



end Lech.PowerSeries


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CoefficientFieldLocalSection
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech
 

theorem finite_module_colength_error_pos (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ (n c : ℕ) (g : A), 0 < n ∧ g ≠ 0 ∧ ∀ I : Ideal A,
      Module.length A (A ⧸ I) ≠ ⊤ →
      |((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) -
        (n : ℝ) * ((Module.length A (A ⧸ I)).toNat : ℝ)| ≤
        (c : ℝ) * ((Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat : ℝ) := by
  obtain ⟨n,c,g,hn,hg,h⟩ := finite_module_colength_compare_pos A M hfaithful
  refine ⟨n,c+n,g,hn,hg,fun I hI => ?_⟩
  obtain ⟨h₁,h₂⟩ := h I hI
  have hG : Module.length A (A ⧸ (I ⊔ Ideal.span {g})) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hI
    let f := I.mapQ (I ⊔ Ideal.span {g}) LinearMap.id le_sup_left
    apply Module.length_le_of_surjective f
    intro x
    obtain ⟨a,rfl⟩ := (I ⊔ Ideal.span {g}).mkQ_surjective x
    exact ⟨I.mkQ a,rfl⟩
  have hM : Module.length A (M ⧸ I • (⊤ : Submodule A M)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ h₁
    exact WithTop.add_ne_top.mpr ⟨WithTop.mul_ne_top (ENat.natCast_ne_top _) hI,
      WithTop.mul_ne_top (ENat.natCast_ne_top _) hG⟩
  rw [← ENat.natCast_toNat hM, ← ENat.natCast_toNat hI,
    ← ENat.natCast_toNat hG] at h₁ h₂
  have hr₁ : ((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) ≤
      (n : ℝ) * (Module.length A (A ⧸ I)).toNat +
      (c : ℝ) * (Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat := by
    exact_mod_cast h₁
  have hr₂ : (n : ℝ) * (Module.length A (A ⧸ I)).toNat ≤
      ((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) +
      (n : ℝ) * (Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat := by
    exact_mod_cast h₂
  have hgn : (0 : ℝ) ≤ (Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat := by positivity
  have hcn : (0 : ℝ) ≤ c := by positivity
  have hnn : (0 : ℝ) ≤ n := by positivity
  rw [Nat.cast_add,abs_le]
  constructor <;> nlinarith

open Filter
open scoped Topology
theorem finite_module_asymptotic_pos (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ (I : ℕ → Ideal A) (u : ℕ → ℝ) (a : ℝ),
      (∀ᶠ q in atTop, Module.length A (A ⧸ I q) ≠ ⊤) →
      (∀ᶠ q in atTop, 0 < u q) →
      Tendsto (fun q => ((Module.length A (A ⧸ I q)).toNat : ℝ) / u q) atTop (𝓝 a) →
      (∀ g : A, g ≠ 0 → Tendsto (fun q =>
        ((Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toNat : ℝ) / u q) atTop (𝓝 0)) →
      Tendsto (fun q => ((Module.length A (M ⧸ I q • (⊤ : Submodule A M))).toNat : ℝ) / u q)
        atTop (𝓝 ((n : ℝ) * a)) := by
  obtain ⟨n,c,g,hn,hg,h⟩ := finite_module_colength_error_pos A M hfaithful
  refine ⟨n,hn,fun I u a hI hu hA hG => ?_⟩
  apply tendsto_of_abs_sub_le (hA.const_mul (n : ℝ))
    (show Tendsto (fun q => (c : ℝ) *
      (((Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toNat : ℝ) / u q)) atTop (𝓝 0) from by
        simpa using (hG g hg).const_mul (c : ℝ))
  filter_upwards [hI,hu] with q hI hu
  have hh := div_le_div_of_nonneg_right (h (I q) hI) hu.le
  simpa only [← mul_div_assoc,← sub_div,abs_div,abs_of_pos hu] using hh

end Lech


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology nonZeroDivisors
variable {k : Type*} [Field k]
 

theorem finite_module_two_limits_pos_oai (h : ℕ) (hh : 0 < h) (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries (Fin h) k) M] [Module.Finite (MvPowerSeries (Fin h) k) M]
    (hfaithful : ∀ g : MvPowerSeries (Fin h) k, g ≠ 0 → g • (LinearMap.id : M →ₗ[MvPowerSeries (Fin h) k] M) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      Tendsto (fun q : ℕ => (h.factorial : ℝ) *
        ((Module.length (MvPowerSeries (Fin h) k)
          (M ⧸ (maximalIdeal (MvPowerSeries (Fin h) k))^q • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) / (q : ℝ)^h)
        atTop (𝓝 (n : ℝ)) ∧
      Tendsto (fun q : ℕ =>
        ((Module.length (MvPowerSeries (Fin h) k)
          (M ⧸ Ideal.span (Set.range (fun i : Fin h => (X i : MvPowerSeries (Fin h) k)^q)) • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) /
          (q : ℝ)^h) atTop (𝓝 (n : ℝ)) := by
  let A := MvPowerSeries (Fin h) k
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let m := maximalIdeal A
  let J (q : ℕ) : Ideal A := Ideal.span (Set.range fun i : Fin h => (X i : A)^q)
  obtain ⟨n,hpos,hn⟩ := Lech.finite_module_asymptotic_pos A M hfaithful
  refine ⟨n,hpos,?_,?_⟩
  · have hbase : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ m^q)).toNat : ℝ) / ((q : ℝ)^h / h.factorial)) atTop (𝓝 1) := by
      apply (Lech.binomial_normalized_tendsto h).congr'
      filter_upwards [eventually_gt_atTop 0] with q hq
      rw [maximal_power_colength h hh q hq]
      simp only [ENat.toNat_natCast,div_div_eq_mul_div]
      ring
    have herr (g : A) (hg : g ≠ 0) : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ (m^q ⊔ Ideal.span {g}))).toNat : ℝ) /
          ((q : ℝ)^h / h.factorial)) atTop (𝓝 0) := by
      have ht := FrobeniusGrowth.ordinary_error_tendsto m
        (Ideal.IsPrime.radical inferInstance) (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
      rw [fin_dimension_nat] at ht
      convert ht.const_mul (h.factorial : ℝ) using 1
      · ext q
        simp only [div_div_eq_mul_div]
        ring
      · simp
    have ht := hn (fun q => m^q) (fun q => (q : ℝ)^h / h.factorial) 1
      (Eventually.of_forall (fun q => Lech.quotient_length_ne_top A q))
      ((eventually_gt_atTop 0).mono (fun q hq => by positivity)) hbase herr
    simp only [mul_one] at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ext q
    simp only [div_div_eq_mul_div]
    ring
  · have hbase : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ J q)).toNat : ℝ) / (q : ℝ)^h) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with q hq
      let : NeZero q := ⟨hq.ne'⟩
      have he := RootTower.variable_powers_colength (σ := Fin h) (k := k) q
      change Module.length A (A ⧸ J q) = _ at he
      rw [he]
      simp only [Fintype.card_fin]
      rw [← Nat.cast_pow, ENat.toNat_natCast, Nat.cast_pow]
      simp [hq.ne']
    have hfinite : ∀ᶠ q in atTop, Module.length A (A ⧸ J q) ≠ ⊤ := by
      filter_upwards [eventually_gt_atTop 0] with q hq
      let : NeZero q := ⟨hq.ne'⟩
      have he := RootTower.variable_powers_colength (σ := Fin h) (k := k) q
      change Module.length A (A ⧸ J q) = _ at he
      rw [he]
      exact ENat.natCast_ne_top _
    have herr (g : A) (hg : g ≠ 0) : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ (J q ⊔ Ideal.span {g}))).toNat : ℝ) / (q : ℝ)^h)
        atTop (𝓝 0) := by
      have ht := FrobeniusGrowth.parameter_error_tendsto h hh (X : Fin h → A)
        maximalIdeal_eq_variables.symm (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
      rwa [fin_dimension_nat] at ht
    have ht := hn J (fun q => (q : ℝ)^h) 1 hfinite
      ((eventually_gt_atTop 0).mono (fun q hq => by positivity)) hbase herr
    simpa only [mul_one] using ht

end Lech.PowerSeries


end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Lech.PowerSeries.finite_module_two_limits_pos_oai.{u_1, u_2} := @OAI.Lech.PowerSeries.finite_module_two_limits_pos_oai.{u_1, u_2}
