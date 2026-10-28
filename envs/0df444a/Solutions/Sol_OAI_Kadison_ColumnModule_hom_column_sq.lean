-- Prove2me | solution 1 for OAI.Kadison.ColumnModule.hom_column_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:18:34.163559+00:00
-- url     : https://prove2.me/submissions/9ae7cac7-fbde-4099-b559-a543908389e2

import Mathlib
import Definitions.Def_OAIQ039C048
import Theorems.Thm_OAI_Kadison_LittleGrothendieck_unitary_norm_le_one

section
-- module Solutions.OAIQ039_CM.Commutator_LittleGrothendieck
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter Set

namespace Kadison.LittleGrothendieck

lemma second_deriv_nonpos {f : ℝ → ℝ} {t d : ℝ}
    (hm : IsLocalMax f t) (hc : ContinuousAt f t)
    (h : HasDerivAt (deriv f) d t) : d ≤ 0 := by
  by_contra! hd
  have hmin := isLocalMin_of_deriv_deriv_pos (by rwa [h.deriv]) hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 t] fun _ => f t := by
    filter_upwards [hm,hmin] with x hx hy
    exact le_antisymm hx hy
  have hz := heq.deriv.deriv_eq
  rw [h.deriv, deriv_const', deriv_const] at hz
  exact (ne_of_gt hd) hz

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem selfAdjoint_square_at_unitary_max
    (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖ ≤ ‖T (u:A)‖)
    (a : A) (ha : IsSelfAdjoint a) :
    ‖T ((u:A)*a)‖^2 ≤ (inner ℂ (T (u:A)) (T ((u:A)*(a*a)))).re := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let b : A := Complex.I • a
  let c : ℝ → A := fun t => (u:A)*NormedSpace.exp (t • b)
  have hc (t : ℝ) : HasDerivAt c (c t*b) t := by
    simpa only [c, mul_assoc] using (hasDerivAt_exp_smul_const b t).const_mul (u:A)
  let v : ℝ → E := fun t => T (c t)
  let v' : ℝ → E := fun t => T (c t*b)
  have hv (t : ℝ) : HasDerivAt v (v' t) t := by
    exact (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hv' (t : ℝ) : HasDerivAt v' (T (c t*b*b)) t := by
    exact (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ((hc t).mul_const b)
  let f : ℝ → ℝ := fun t => ‖v t‖^2
  have hf (t : ℝ) : HasDerivAt f (2*(inner ℂ (v t) (v' t)).re) t := by
    simpa only [f, real_inner_eq_re_inner ℂ, ← RCLike.re_to_complex] using (hv t).norm_sq
  have hfun : deriv f=fun t => 2*(inner ℂ (v t) (v' t)).re := by
    funext t
    exact (hf t).deriv
  have hsecond : HasDerivAt (deriv f)
      (2*((inner ℂ (v' 0) (v' 0)).re+
          (inner ℂ (v 0) (T (c 0*b*b))).re)) 0 := by
    rw [hfun]
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.add_re, add_comm] using
      ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
        ((hv 0).inner ℂ (hv' 0))).const_mul 2)
  have hmax : IsLocalMax f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have ht : NormedSpace.exp (t • b) ∈ unitary A := by
      change NormedSpace.exp (t • (Complex.I • a)) ∈ unitary A
      have hs : IsSelfAdjoint (t • a) := (IsSelfAdjoint.all t).smul ha
      rw [smul_comm t Complex.I a]
      exact (selfAdjoint.expUnitary (⟨t • a,hs⟩ : selfAdjoint A)).property
    have hh := hu (u*⟨NormedSpace.exp (t • b),ht⟩)
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa only [f,v,c,zero_smul,NormedSpace.exp_zero,mul_one,Submonoid.coe_mul] using hh
  have hs := second_deriv_nonpos hmax (hf 0).continuousAt hsecond
  have hzero : c 0=(u:A) := by simp [c]
  have hbb : b*b=-(a*a) := by
    simp only [b,smul_mul_assoc,mul_smul_comm,smul_smul,Complex.I_mul_I,neg_one_smul]
  have hb2 : c 0*b*b=-((u:A)*(a*a)) := by rw [hzero,mul_assoc,hbb,mul_neg]
  have hvzero : v 0=T (u:A) := by simp only [v,hzero]
  have hv'zero : v' 0=Complex.I • T ((u:A)*a) := by
    simp only [v',hzero,b,mul_smul_comm,map_smul]
  rw [hvzero,hv'zero,hb2,map_neg,inner_neg_right,Complex.neg_re] at hs
  have hi : (inner ℂ (Complex.I • T ((u:A)*a)) (Complex.I • T ((u:A)*a))).re =
      ‖T ((u:A)*a)‖^2 := by simp [norm_smul, ← Complex.ofReal_pow]
  rw [hi] at hs
  linarith

end Kadison.LittleGrothendieck

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ColumnModule
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace CStarAlgebra

open Filter Set

namespace Kadison.ColumnModule

variable {A E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma regularized_factor (a : A) {ε : ℝ} (hε : 0<ε) :
    ∃ b c : A, ‖b‖≤ 1 ∧ IsSelfAdjoint c ∧
      c*c=star a*a+ε • (1:A) ∧ a=b*c := by
  let d := star a*a+ε • (1:A)
  have hd : IsStrictlyPositive d := by
    simpa only [d,add_comm] using
      (IsStrictlyPositive.smul hε (isStrictlyPositive_one (A:=A))).add_nonneg
        (star_mul_self_nonneg a)
  let c := CFC.sqrt d
  have hc : IsSelfAdjoint c := (CFC.sqrt_nonneg d).isSelfAdjoint
  have hcunit : IsUnit c := CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hd
  let v : Aˣ := hcunit.unit
  have hv : (v:A)=c := hcunit.unit_spec
  have hvs : star (v:A)=(v:A) := by rw [hv]; exact hc.star_eq
  have hivi : star ((v⁻¹:Aˣ):A)=((v⁻¹:Aˣ):A) := by
    have ht : star v=v := Units.ext hvs
    change ((star (v⁻¹):Aˣ):A)=((v⁻¹:Aˣ):A)
    rw [star_inv,ht]
  let b := a*((v⁻¹:Aˣ):A)
  have hcc : c*c=d := CFC.sqrt_mul_sqrt_self d hd.nonneg
  have hs : star b*b≤ 1 := by
    have hle : star a*a ≤ d := le_add_of_nonneg_right (smul_nonneg hε.le zero_le_one)
    have hh := star_left_conjugate_le_conjugate hle (((v⁻¹:Aˣ):A))
    have he : star ((v⁻¹:Aˣ):A)*d*((v⁻¹:Aˣ):A)=1 := by
      rw [hivi,←hcc,←hv]
      simp only [←mul_assoc,Units.inv_mul,one_mul,Units.mul_inv]
    rw [he] at hh
    simpa only [b,star_mul,mul_assoc] using hh
  have hn : ‖b‖≤ 1 := by
    have hh := (CStarAlgebra.norm_le_one_iff_of_nonneg (star b*b)
      (star_mul_self_nonneg b)).mpr hs
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg b]
  refine ⟨b,c,hn,hc,hcc,?_⟩
  simp only [b,←hv,mul_assoc,Units.inv_mul,mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjoint_square_max (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖)
    (a : A) (ha : IsSelfAdjoint a) :
    ‖T (a*(u:A))‖^2 ≤ (inner ℂ (T (u:A)) (T ((a*a)*(u:A)))).re := by
  let S : A →L[ℂ] E := T.comp ((ContinuousLinearMap.mul ℂ A).flip (u:A))
  have hS : ∀ v : unitary A, ‖S (v:A)‖≤‖S (1:A)‖ := by
    intro v
    simpa only [S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply',one_mul,Submonoid.coe_mul] using hu (v*u)
  simpa only [S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',OneMemClass.coe_one,one_mul] using
      LittleGrothendieck.selfAdjoint_square_at_unitary_max S 1 hS a ha

lemma maxFunctional_nonneg (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖) {a : A} (ha : 0≤a) :
    0≤ maxFunctional T u a := by
  have h := selfAdjoint_square_max T u hu (CFC.sqrt a)
    (CFC.sqrt_nonneg a).isSelfAdjoint
  rw [CFC.sqrt_mul_sqrt_self a ha] at h
  exact (sq_nonneg _).trans h

lemma maxFunctional_mono (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖) :
    Monotone (maxFunctional T u) := by
  intro a b hab
  have h := maxFunctional_nonneg T u hu (sub_nonneg.mpr hab)
  rwa [map_sub,sub_nonneg] at h

lemma maxFunctional_bound (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖) {a : A}
    (ha : IsSelfAdjoint a) : maxFunctional T u a≤‖a‖*‖T (u:A)‖^2 := by
  have h := maxFunctional_mono T u hu ha.le_algebraMap_norm_self
  simpa only [Algebra.algebraMap_eq_smul_one,map_smul,maxFunctional_one,smul_eq_mul] using h

lemma module_square_max (T : A →L[ℂ] E) {M : ℝ} (hM : 0≤ M)
    (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (u : unitary A) (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖)
    (a : A) : ‖T (a*(u:A))‖^2≤ M^2*maxFunctional T u (star a*a) := by
  have heps (ε : ℝ) (hε : 0<ε) :
      ‖T (a*(u:A))‖^2≤ M^2*(maxFunctional T u (star a*a)+ε*maxFunctional T u 1) := by
    obtain ⟨b,c,hb,hc,hcc,hbc⟩ := regularized_factor a hε
    have hn : ‖T (a*(u:A))‖≤ M*‖T (c*(u:A))‖ := by
      rw [hbc,mul_assoc]
      exact (hmod b (c*(u:A))).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb hM) (norm_nonneg (T (c*(u:A)))))
    have hs := selfAdjoint_square_max T u hu c hc
    change ‖T (c*(u:A))‖^2≤ maxFunctional T u (c*c) at hs
    rw [hcc,map_add,map_smul,smul_eq_mul] at hs
    calc
      _ ≤ (M*‖T (c*(u:A))‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = M^2*‖T (c*(u:A))‖^2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg M)
  have hlim : Tendsto
      (fun ε : ℝ => M^2*(maxFunctional T u (star a*a)+ε*maxFunctional T u 1))
      (𝓝[>] 0) (𝓝 (M^2*maxFunctional T u (star a*a))) := by
    have h : Continuous (fun ε : ℝ => M^2*(maxFunctional T u (star a*a)+ε*maxFunctional T u 1)) := by
      fun_prop
    simpa only [zero_mul,add_zero] using
      (h.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.eventually_of_mem self_mem_nhdsWithin heps)

theorem sum_sq_at_max {ι : Type*} [Fintype ι]
    (T : A →L[ℂ] E) {M : ℝ} (hM : 0≤ M)
    (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (u : unitary A) (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖)
    (a : ι → A) : ∑ i, ‖T (a i)‖^2≤ M^2*‖T‖^2*‖∑ i,star (a i)*a i‖ := by
  classical
  let b : ι → A := fun i => a i*(star u:A)
  have hb (i : ι) : b i*(u:A)=a i := by
    simp only [b,mul_assoc,Unitary.star_mul_self_of_mem u.property,mul_one]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => module_square_max T hM hmod u hu (b i))
  simp only [hb,←Finset.mul_sum,←map_sum] at hs
  have hpos : 0≤∑ i,star (b i)*b i := Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have hn : ‖∑ i,star (b i)*b i‖=‖∑ i,star (a i)*a i‖ := by
    have he : (∑ i,star (b i)*b i)=(u:A)*(∑ i,star (a i)*a i)*(star u:A) := by
      simp only [b,star_mul,star_star,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [he]
    change ‖(u:A)*(∑ i,star (a i)*a i)*(↑(star u):A)‖=_
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  have huT : ‖T (u:A)‖≤‖T‖ := by
    cases subsingleton_or_nontrivial A with
    | inl h => simpa only [Subsingleton.elim (u:A) 0,map_zero,norm_zero] using norm_nonneg T
    | inr h => simpa only [CStarRing.norm_coe_unitary,mul_one] using T.le_opNorm (u:A)
  calc
    _ ≤ M^2*maxFunctional T u (∑ i,star (b i)*b i) := hs
    _ ≤ M^2*(‖∑ i,star (b i)*b i‖*‖T (u:A)‖^2) :=
      mul_le_mul_of_nonneg_left (maxFunctional_bound T u hu hpos.isSelfAdjoint) (sq_nonneg M)
    _ ≤ M^2*(‖∑ i,star (b i)*b i‖*‖T‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) huT 2) (norm_nonneg _)) (sq_nonneg M)
    _ = _ := by rw [hn]; ring

end Kadison.ColumnModule

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma norm_coe_tendsto (x : Pre ω H) :
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 ‖(x : Space ω H)‖) := by
  rw [Completion.norm_coe]
  exact tendsto_norm ω H x

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_LittleGrothendieckSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.LittleGrothendieck

open HilbertSequence

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma sequenceMap_norm_le (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) :
    ‖sequenceMap ω T‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [sequenceMap_apply, Completion.norm_coe]
  exact sequenceLinear_bound ω T x

lemma sequenceMap_norm_tendsto (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) (x : ℕ →ᵇ A) :
    Tendsto (fun n => ‖T (x n)‖) (ω : Filter ℕ) (𝓝 ‖sequenceMap ω T x‖) :=
  norm_coe_tendsto ω E (sequenceLinear ω T x)

lemma sequenceMap_const (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) (x : A) :
    sequenceMap ω T (BoundedContinuousFunction.const ℕ x)=constant ω E (T x) := rfl

theorem exists_sequence_unitary_max (T : A →L[ℂ] E) :
    ∃ (ω : Ultrafilter ℕ) (u : unitary (ℕ →ᵇ A)),
      ∀ v : unitary (ℕ →ᵇ A), ‖sequenceMap ω T (v:ℕ →ᵇ A)‖ ≤
        ‖sequenceMap ω T (u:ℕ →ᵇ A)‖ := by
  classical
  let S : Set ℝ := range (fun u : unitary A => ‖T (u:A)‖)
  have hSne : S.Nonempty := ⟨‖T (1:A)‖,1,rfl⟩
  have hSb : BddAbove S := ⟨‖T‖,by
    rintro r ⟨u,rfl⟩
    exact (T.le_opNorm _).trans (by nlinarith [unitary_norm_le_one u, norm_nonneg T])⟩
  obtain ⟨r,_,hr,hmem⟩ := exists_seq_tendsto_sSup hSne hSb
  choose u hu using hmem
  let U : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (u n:A)) 1 (fun n => unitary_norm_le_one (u n))
  have hU : U ∈ unitary (ℕ →ᵇ A) := by
    constructor <;> apply BoundedContinuousFunction.ext <;> intro n
    · exact Unitary.coe_star_mul_self (u n)
    · exact Unitary.coe_mul_star_self (u n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le _
  have hlim : ‖sequenceMap ω T U‖=sSup S := by
    apply tendsto_nhds_unique (sequenceMap_norm_tendsto ω T U)
    change Tendsto (fun n => ‖T (u n:A)‖) (ω : Filter ℕ) (𝓝 (sSup S))
    simpa only [hu] using hr.mono_left hω
  refine ⟨ω,⟨U,hU⟩,fun v => ?_⟩
  rw [show (⟨U,hU⟩ : unitary (ℕ →ᵇ A)).val=U from rfl,hlim]
  apply le_of_tendsto (sequenceMap_norm_tendsto ω T (v:ℕ →ᵇ A))
  apply Filter.Eventually.of_forall
  intro n
  have hv : (v:ℕ →ᵇ A) n ∈ unitary A := by
    constructor
    · exact congrArg (fun f : ℕ →ᵇ A => f n) (Unitary.coe_star_mul_self v)
    · exact congrArg (fun f : ℕ →ᵇ A => f n) (Unitary.coe_mul_star_self v)
  exact le_csSup hSb ⟨⟨(v:ℕ →ᵇ A) n,hv⟩,rfl⟩

end Kadison.LittleGrothendieck

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ColumnEstimate
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.ColumnModule

open LittleGrothendieck HilbertSequence

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma sequence_module_bound (ω : Ultrafilter ℕ) (T : A →L[ℂ] E)
    {M : ℝ} (hM : 0≤M) (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (a b : ℕ →ᵇ A) :
    ‖sequenceMap ω T (a*b)‖≤ M*‖a‖*‖sequenceMap ω T b‖ := by
  apply le_of_tendsto_of_tendsto (sequenceMap_norm_tendsto ω T (a*b))
    (tendsto_const_nhds.mul (sequenceMap_norm_tendsto ω T b))
  apply Filter.Eventually.of_forall
  intro n
  exact (hmod (a n) (b n)).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (a.norm_coe_le_norm n) hM) (norm_nonneg _))

theorem sum_norm_sq_le {ι : Type*} [Fintype ι] (T : A →L[ℂ] E)
    {M : ℝ} (hM : 0≤M) (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (a : ι → A) : ∑ i, ‖T (a i)‖^2≤ M^2*‖T‖^2*‖∑ i,star (a i)*a i‖ := by
  classical
  obtain ⟨ω,u,hu⟩ := exists_sequence_unitary_max T
  let : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _
  have h := sum_sq_at_max (sequenceMap ω T) hM (sequence_module_bound ω T hM hmod)
    u hu (fun i => BoundedContinuousFunction.const ℕ (a i))
  simp only [sequenceMap_const,LinearIsometry.norm_map] at h
  have hc : (∑ i,star (BoundedContinuousFunction.const ℕ (a i))*
      BoundedContinuousFunction.const ℕ (a i))=
      BoundedContinuousFunction.const ℕ (∑ i,star (a i)*a i) := by
    ext n
    simp
  rw [hc,BoundedContinuousFunction.norm_const_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (sequenceMap_norm_le ω T) 2) (sq_nonneg M)) (norm_nonneg _))

lemma homOrbit_norm (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (ξ : E) : ‖homOrbit φ hM hφ ξ‖≤ M*‖ξ‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg hM (norm_nonneg ξ)) _

theorem hom_column_sq_oai {ι : Type*} [Fintype ι]
    (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (a : ι → A) (ξ : E) :
    ∑ i, ‖φ (a i) ξ‖^2 ≤ M^4*‖ξ‖^2*‖∑ i,star (a i)*a i‖ := by
  have hm (a b : A) : ‖homOrbit φ hM hφ ξ (a*b)‖≤ M*‖a‖*‖homOrbit φ hM hφ ξ b‖ := by
    simp only [homOrbit_apply,map_mul,mul_apply_eq_comp]
    exact ((φ a).le_opNorm (φ b ξ)).trans
      (mul_le_mul_of_nonneg_right (hφ a) (norm_nonneg _))
  have h := sum_norm_sq_le (homOrbit φ hM hφ ξ) hM hm a
  calc
    _ ≤ M^2*‖homOrbit φ hM hφ ξ‖^2*‖∑ i,star (a i)*a i‖ := h
    _ ≤ M^2*(M*‖ξ‖)^2*‖∑ i,star (a i)*a i‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (homOrbit_norm φ hM hφ ξ) 2) (sq_nonneg M)) (norm_nonneg _)
    _ = _ := by ring

end Kadison.ColumnModule

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.ColumnModule.hom_column_sq_oai.{u_1, u_2, u_3} := @OAI.Kadison.ColumnModule.hom_column_sq_oai.{u_1, u_2, u_3}
