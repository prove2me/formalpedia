-- Prove2me | solution 1 for OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:05.690224+00:00
-- url     : https://prove2.me/submissions/761e527f-8fd5-41ce-8f54-25f709dca677

import Mathlib
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom014
import Definitions.Def_OAIQ368Chrom024

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalPureCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]

lemma pureRatio_neg (v : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) (pureRatio v (-t))=(pureRatio v t)⁻¹ := by
  apply mul_left_cancel (a:=pureRatio v t)
  rw [←pureRatio_add,add_neg_cancel,pureRatio_zero,mul_inv_cancel]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open WallUnits PowerSeries
noncomputable section
variable {K : Type*} [Field K]
variable (v : Kˣ)
lemma shiftedElementary_zero : shiftedElementary v 0=
    elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K) := by
  simp [shiftedElementary]
lemma shiftedElementary_step
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    shiftedElementary v t=(1+C (↑(v^(-2*t-1)):K)*X)*shiftedElementary v (t+1) := by
  conv_lhs => rw [shiftedElementary,elementary_tail _ _ hq]
  rw [_root_.map_mul,_root_.map_add,_root_.map_one,_root_.map_mul,rescale_C,rescale_X,rescale_rescale]
  rw [←mul_assoc,←(PowerSeries.C (R:=K)).map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  have H1 : -1+(-2*t)= -2*t-1:=by ring
  rw [H1]
  unfold shiftedElementary
  simp only [zpow_neg_one]
  congr 2
  rw [←Units.val_mul,←zpow_add]
  congr 2
  ring_nf
lemma expandedPure_step (t : ℤ) :
    expandZero (pureRatio v (t+1):RatFunc K)=
      expandZero (pureRatio v t:RatFunc K)*
        HahnSeries.ofPowerSeries ℤ K (1+C (↑(v^(-2*t-1)):K)*X) := by
  rw [pureRatio_add,Units.val_mul,pureRatio_one,scaleAction_val]
  change expandZero ((pureRatio v t:RatFunc K)*
    scale (v^(-2*t)) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X))=_
  rw [_root_.map_add,_root_.map_one,_root_.map_mul,_root_.map_mul,scale_constant,scale_X,
    ←mul_assoc,←RatFunc.C.map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  rw [show -1+(-2*t)= -2*t-1 by ring]
  simp only [_root_.map_mul,_root_.map_add,_root_.map_one,expandZero_constant,
    expandZero_X,HahnSeries.ofPowerSeries_C,HahnSeries.ofPowerSeries_X]
lemma expandedPure_times_shift
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandZero (pureRatio v t:RatFunc K)*
      HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t)=
        HahnSeries.ofPowerSeries ℤ K (shiftedElementary v 0) := by
  induction t using Int.induction_on with
  | zero=>simp
  | succ t ih=>
    rw [expandedPure_step,mul_assoc,←_root_.map_mul,←shiftedElementary_step v hq]
    exact ih
  | pred t ih=>
    rw [shiftedElementary_step v hq (-↑t-1)]
    have H : (-↑t-1)+(1:ℤ)= -↑t:=by ring
    rw [H,_root_.map_mul,←mul_assoc,←expandedPure_step,H]
    exact ih
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma split_injective {m n : M} (hk : k m=k n) (ho : off k p hp m=off k p hp n) : m=n := by
  rw [←split_sum k p hp m,←split_sum k p hp n,hk,ho]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance rationalLaurentFaithfulRing_r4ae8d5_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalLaurentFaithfulNonUnitalNonAssocSemiring
lemma expandFiber_monomial_coeff (l : k.ker) (a : RatFunc K) (n : ℤ) :
    (expandFiber v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=
      Torus.monomial v Ω (n • p+(l:M)) ((expandZero a).coeff n*(↑(v^(n*Ω p l)):K)) := by
  change (expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=_
  rw [expandFiberAdd_monomial,HahnSeries.coeff_mul_single_zero]
  change Torus.monomial v Ω (n • p) ((expandZero a).coeff n)*Torus.X v Ω l=_
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,map_zsmul,AddMonoidHom.zsmul_apply,
    smul_eq_mul]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegradeFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeFaithfulRing
local instance regradeFaithfulAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeFaithfulAddGroup_r4ae8d5_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma regrade_read (τ : M →+ ℤ) {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hτ : FullHomogeneous v Ω τ f)
    (n : ℕ) (m : M) (hm : τ m=(n:ℤ)) :
    coeff (δ m).toNat (regrade v Ω δ B f) m=coeff n f m := by
  classical
  rw [regrade_coeff_eval,ite_eq_left rfl]
  apply Finset.sum_eq_single n
  · intro j hj hne
    by_contra hz
    have H:=hτ j m hz
    have : j=n:=by omega
    exact hne this
  · intro hn
    by_contra hz
    have H:=(hf n m hz).2
    have HH : ¬n<B*(δ m).toNat+1:=by simpa only [Finset.mem_range] using hn
    omega

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentPureAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_2
local instance instAddCommMonoidTorus_r4ae8d5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus_2
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus_2
lemma purePower_eq (f : PowerSeries K) :
    purePower v Ω hΩ p f=HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f) := by
  apply HahnSeries.ext
  funext n
  change Torus.monomial v Ω (n • p) ((HahnSeries.ofPowerSeries ℤ K f).coeff n)=_
  rcases le_or_gt 0 n with hn|hn
  · lift n to ℕ using hn with j hj
    rw [HahnSeries.ofPowerSeries_apply_coeff,HahnSeries.ofPowerSeries_apply_coeff,coeff_raySeries]
    simp only [natCast_zsmul]
  · have H : (HahnSeries.ofPowerSeries ℤ K f).coeff n=0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a,ha⟩
      change (a:ℤ)=n at ha
      omega
    have H' : (HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f)).coeff n=0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a,ha⟩
      change (a:ℤ)=n at ha
      omega
    rw [H,H',Torus.monomial_zero]
lemma purePower_commutation (m : M) (f : PowerSeries K) :
    HahnSeries.single 0 (Torus.X v Ω m)*purePower v Ω hΩ p f=
      purePower v Ω hΩ p (rescale (↑(v^(-2*Ω p m)):K) f)*
        HahnSeries.single 0 (Torus.X v Ω m) := by
  have H:=raySeries_twist v Ω hΩ p m (rescale (↑(v^(-2*Ω p m)):K) f)
  rw [rescale_rescale,←Units.val_mul,←zpow_add,
    show -2*Ω p m+2*Ω p m=0 by ring,zpow_zero,Units.val_one,rescale_one] at H
  have HH:=congrArg (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) H
  rw [purePower_eq,purePower_eq]
  simpa only [map_mul,HahnSeries.ofPowerSeries_C,HahnSeries.C_apply,RingHom.id_apply] using HH.symm
lemma purePower_scalar_commute (a : RatFunc K) (f : PowerSeries K) :
    expandScalar v Ω hΩ p a*purePower v Ω hΩ p f=
      purePower v Ω hΩ p f*expandScalar v Ω hΩ p a := by
  change (laurentRayHom v Ω p (hΩ p)) (expandZero a)*
    (laurentRayHom v Ω p (hΩ p)) (HahnSeries.ofPowerSeries ℤ K f)=_
  rw [←map_mul,mul_comm,map_mul]
  rfl
lemma expandedPure_shifted
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandScalar v Ω hΩ p (pureRatio v t:RatFunc K)*
      purePower v Ω hΩ p (shiftedElementary v t)=purePower v Ω hΩ p (shiftedElementary v 0) := by
  have H:=congrArg (laurentRayHom v Ω p (hΩ p)) (expandedPure_times_shift v hq t)
  simpa only [map_mul,expandScalar,purePower,RingHom.comp_apply] using H

variable (k : M →+ ℤ)
lemma expand_pure_intertwine
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiber v Ω hΩ k p (pureAction v (complementOmega k Ω) (complementAlpha k p Ω) f)*
      (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))=
    (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*expandFiber v Ω hΩ k p f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,add_mul,mul_add,hf,hg]
  | single l a=>
    change expandFiber v Ω hΩ k p
      (pureAction v _ _ (FiberTorus.monomial v _ _ l a))*_=_
    rw [pureAction_monomial]
    change expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l
      (a*(pureRatio v (Ω p l):RatFunc K)))*_= _*expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)
    rw [expandFiberAdd_monomial,expandFiberAdd_monomial]
    change (expandScalar v Ω hΩ p (a*(pureRatio v (Ω p l):RatFunc K))*
      HahnSeries.single 0 (Torus.X v Ω l))*purePower v Ω hΩ p (shiftedElementary v 0)=
      purePower v Ω hΩ p (shiftedElementary v 0)*
        (expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l))
    rw [map_mul,mul_assoc,mul_assoc,purePower_commutation]
    have H : rescale (↑(v^(-2*Ω p l)):K) (shiftedElementary v 0)=shiftedElementary v (Ω p l) := by
      rw [shiftedElementary_zero]
      rfl
    rw [H,←mul_assoc (expandScalar v Ω hΩ p (pureRatio v (Ω p l):RatFunc K)),
      expandedPure_shifted v Ω hΩ p hq,←mul_assoc,purePower_scalar_commute,mul_assoc]
lemma expand_pure_conjugate
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiber v Ω hΩ k p (pureAction v (complementOmega k Ω) (complementAlpha k p Ω) f)=
      innerHom (pureLaurentUnit v Ω hΩ p) (expandFiber v Ω hΩ k p f) := by
  have H:=congrArg (fun x : HahnSeries ℤ (Torus v Ω)=>x*↑((pureLaurentUnit v Ω hΩ p)⁻¹))
    (expand_pure_intertwine v Ω hΩ p k hq f)
  have hu : (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*↑((pureLaurentUnit v Ω hΩ p)⁻¹)=1 :=
    (pureLaurentUnit v Ω hΩ p).val_inv
  change _=(↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*
    expandFiber v Ω hΩ k p f*↑((pureLaurentUnit v Ω hΩ p)⁻¹)
  simpa only [mul_assoc,hu,mul_one] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRegradeFinite
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B D : ℕ)

lemma sum_range_eq_of_tails_zero {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (a b : ℕ) (ha : ∀n,a≤n → f n=0) (hb : ∀n,b≤n → f n=0) :
    ∑n∈Finset.range a,f n=∑n∈Finset.range b,f n := by
  have H (c : ℕ) (hc : c ≤ max a b) (h : ∀n,c≤n → f n=0) :
      ∑n∈Finset.range c,f n=∑n∈Finset.range (max a b),f n := by
    apply Finset.sum_subset (Finset.range_mono hc)
    intro n hn hnc
    exact h n (by simpa only [Finset.mem_range,not_lt] using hnc)
  exact (H a (le_max_left _ _) ha).trans (H b (le_max_right _ _) hb).symm

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentRegradeFiniteRing
local instance laurentRegradeFiniteAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradeFiniteAddGroup_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma laurentRegrade_finite {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : RegradeBound v Ω δ D f) (d : ℕ) :
    coeff d (laurentRegrade v Ω δ κ B f hf)=
      coeff d (laurentHomogenize v Ω δ κ (coeff d (regrade v Ω δ D f))) := by
  apply HahnSeries.ext
  funext z
  ext m
  rw [laurentRegrade_coeff,nonp_torus_eval_sum,laurentHomogenize_coeff]
  by_cases h : d=(δ m).toNat ∧ z=κ m
  · rw [ite_eq_left h,regrade_coeff_eval,ite_eq_left h.1]
    simp_rw [laurentHomogenize_coeff,ite_eq_left h]
    apply sum_range_eq_of_tails_zero
    · intro n hn
      by_contra hm
      obtain ⟨hd,hk,he⟩:=hf n m hm
      have hD : δ m=(d:ℤ) := by rw [h.1,Int.toNat_of_nonneg hd]
      rw [hD,←h.2] at he
      omega
    · intro n hn
      by_contra hm
      have H:=(hg n m hm).2
      rw [←h.1] at H
      omega
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro n hn
    rw [laurentHomogenize_coeff,ite_eq_right h]

lemma laurentRegrade_finite_read {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : RegradeBound v Ω δ D f)
    (d : ℕ) (z : ℤ) (m : M) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z m=
      if z=κ m then coeff d (regrade v Ω δ D f) m else 0 := by
  rw [laurentRegrade_finite v Ω δ κ B D hf hg,laurentHomogenize_coeff]
  by_cases he : d=(δ m).toNat
  · simp only [he,true_and]
  · rw [regrade_coeff_eval,ite_eq_right he]
    simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRegradePure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
variable (p : M) (hδ : δ p=0) (hκ : κ p=1)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentRegradePureRing
local instance laurentRegradePureAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradePureAddGroup_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
include hδ hκ in
lemma laurentRegrade_pure (f : PowerSeries R) :
    laurentRegrade v Ω δ κ B (raySeries v Ω p f)
      (pure_laurentBounded v Ω δ κ B p hδ hκ f)=
    PowerSeries.C (HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f)) := by
  classical
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  rw [laurentRegrade_coeff]
  simp_rw [coeff_raySeries,laurentHomogenize_monomial]
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one,mul_zero,Int.toNat_zero,coeff_monomial]
  by_cases hd : d=0
  · subst d
    simp only [coeff_C,Nat.cast_zero,mul_zero,add_zero,ite_true, if_true]
    by_cases hz : 0≤z
    · lift z to ℕ using hz with j hj
      simp [HahnSeries.coeff_single]
    · have hz' : z<0 := lt_of_not_ge hz
      have H (j : ℕ) : z≠(j:ℤ) := by omega
      simp_rw [HahnSeries.coeff_single,ite_eq_right (H _)]
      rw [Finset.sum_const_zero,HahnSeries.ofPowerSeries_apply,HahnSeries.embDomain_of_notMem_range]
      rintro ⟨n,hn⟩
      simp only [Nat.castOrderEmbedding_apply] at hn
      omega
  · simp only [ite_eq_right hd,HahnSeries.coeff_zero,Finset.sum_const_zero,coeff_C]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCocycleExt
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K] (v : Kˣ)
lemma cocycle_eq_zpow (c : ℤ → (RatFunc K)ˣ) (h0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u)) (t : ℤ) :
    c t=((⟨c 1,Multiplicative.ofAdd 1⟩ : PureExtension v)^t).left := by
  have H:=map_zpow (cocycleLift v c h0 hc) (Multiplicative.ofAdd 1) t
  rw [←ofAdd_zsmul,smul_eq_mul,mul_one] at H
  exact congrArg SemidirectProduct.left H
lemma cocycle_ext (c d : ℤ → (RatFunc K)ˣ) (hc0 : c 0=1) (hd0 : d 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u))
    (hd : ∀t u,d (t+u)=d t*scaleAction v (Multiplicative.ofAdd t) (d u))
    (h1 : c 1=d 1) : c=d := by
  funext t
  rw [cocycle_eq_zpow v c hc0 hc,cocycle_eq_zpow v d hd0 hd,h1]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCutIdentity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
lemma oppositeInverseRatio_one_val : (oppositeInverseRatio v 1:RatFunc K)=
    1+RatFunc.C (v:K)*(RatFunc.X:RatFunc K)⁻¹ := by
  have H:=pureRatio_neg v (-1)
  change scaleAction v (Multiplicative.ofAdd (-1)) (pureRatio v 1)=(pureRatio v (-1))⁻¹ at H
  rw [pureRatio_one] at H
  change reciprocal (↑((pureRatio v (-1))⁻¹):RatFunc K)=_
  rw [←H,scaleAction_val]
  change reciprocal (scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X))=_
  simp only [map_add,map_one,map_mul,scale_constant,scale_X,
    reciprocal_constant,reciprocal_X]
  rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  norm_num
lemma cutRatio_one : shearRatio v 1*pureRatio v 1=oppositeInverseRatio v 1 := by
  apply Units.ext
  rw [Units.val_mul,shearRatio_val,pureRatio_one,oppositeInverseRatio_one_val]
  change RatFunc.C (↑(v^((1:ℤ)*1)):K)*RatFunc.X^(-(1:ℤ))*
    (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=_
  simp only [mul_one,zpow_one,zpow_neg_one,Units.val_inv_eq_inv_val,map_inv₀]
  have hx : (RatFunc.X:RatFunc K)≠0:=RatFunc.X_ne_zero
  have hv : RatFunc.C (v:K)≠0:=(map_ne_zero RatFunc.C).2 v.ne_zero
  field_simp
  ring
lemma cutRatio (t : ℤ) : shearRatio v t*pureRatio v t=oppositeInverseRatio v t := by
  have H:=cocycle_ext v (fun t=>shearRatio v t*pureRatio v t) (oppositeInverseRatio v)
    (by simp) (by simp) (by
      intro t u
      rw [shearRatio_add,pureRatio_add,map_mul]
      simp only [mul_assoc,mul_left_comm,mul_comm]) (oppositeInverseRatio_add v) (cutRatio_one v)
  exact congrFun H t

variable (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
lemma rational_cut_identity :
    (shearActionHom v Ω α).comp (pureActionHom v Ω α)=oppositeInverseActionHom v Ω α := by
  apply RingHom.ext
  intro f
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=
    FiberTorus.gaugeAdd v Ω α _ f
  rw [FiberTorus.gauge_comp]
  have HH : (fun t=>(pureRatio v t:RatFunc K)*(shearRatio v t:RatFunc K))=
      fun t=>(oppositeInverseRatio v t:RatFunc K) := by
    funext t
    rw [mul_comm,←Units.val_mul,cutRatio]
  rw [HH]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalCenteredAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits Polynomial
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)

variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma complement_pairing (m : M) : complementAlpha k p Ω (off k p hp m)=Ω p m := by
  change Ω p (m-k m • p)=_
  rw [map_sub,map_zsmul,hΩ,smul_zero,sub_zero]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalShearEmbedding
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma centeredScalar_shear (n t : ℤ) :
    centeredScalar v (n-t) t=centeredScalar v n t*(shearRatio v t:RatFunc K) := by
  rw [shearRatio_val,centeredScalar,centeredScalar]
  rw [show -(n-t)*t= -n*t+t*t by ring,zpow_add,Units.val_mul,map_mul,
    sub_eq_add_neg,zpow_add₀ RatFunc.X_ne_zero]
  ring
include hΩ in
lemma shearAction_embed_monomial (m : M) (a : K) :
    shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.monomial v Ω m a))=
      embed v Ω hΩ k p hp (Torus.monomial v Ω (mutationShear Ω p m) a) := by
  rw [embed_monomial,embed_monomial]
  change FiberTorus.gauge v _ _ _ _ _ (FiberTorus.monomial v _ _ _ _)=_
  rw [FiberTorus.gauge_monomial]
  have Hoff : off k p hp (mutationShear Ω p m)=off k p hp m := by
    change off k p hp (m-Ω p m • p)=_
    rw [map_sub,map_zsmul,off_p,smul_zero,sub_zero]
  have Hk : k (mutationShear Ω p m)=k m-Ω p m := by
    change k (m-Ω p m • p)=_
    rw [map_sub,map_zsmul,hp,smul_eq_mul,mul_one]
  rw [Hoff,Hk,complement_pairing Ω hΩ k p hp m,centeredScalar_shear]
  rw [mul_assoc]
include hΩ in
lemma shearAction_embed (f : Torus v Ω) :
    shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp f)=
      embed v Ω hΩ k p hp
        (Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) f) := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change _=embed v Ω hΩ k p hp (Torus.push v Ω Ω _ _ (Torus.monomial v Ω m a))
    rw [Torus.push_monomial]
    exact shearAction_embed_monomial v Ω hΩ k p hp m a
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_4
local instance instNonUnitalSemiringTorus_4_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_4_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma completed_expand_pure
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (completedPureAction v _ _ f)=
      innerHom (completedPureUnit v Ω hΩ p) (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  apply PowerSeries.ext
  intro d
  change expandFiber v Ω hΩ k p
    (coeff d (completedPureAction v (complementOmega k Ω) (complementAlpha k p Ω) f))=
    coeff d (PowerSeries.C (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*
      PowerSeries.map (expandFiber v Ω hΩ k p) f*
        PowerSeries.C (↑((pureLaurentUnit v Ω hΩ p)⁻¹):HahnSeries ℤ (Torus v Ω)))
  change expandFiber v Ω hΩ k p
    (coeff d (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom f))=_
  rw [coeff_map,coeff_mul_C,coeff_C_mul,coeff_map]
  exact expand_pure_conjugate v Ω hΩ p k hq (coeff d f)
lemma innerHom_one {A : Type*} [Ring A] (a : A) : innerHom (1:Aˣ) a=a := by
  simp [innerHom]
lemma innerHom_mul {A : Type*} [Ring A] (u w : Aˣ) (a : A) :
    innerHom (u*w) a=innerHom u (innerHom w a) := by
  simp [innerHom,mul_assoc]
lemma innerHom_inv_cancel {A : Type*} [Ring A] (u : Aˣ) (a : A) :
    innerHom u⁻¹ (innerHom u a)=a := by
  rw [←innerHom_mul,inv_mul_cancel,innerHom_one]
lemma innerHom_cancel_inv {A : Type*} [Ring A] (u : Aˣ) (a : A) :
    innerHom u (innerHom u⁻¹ a)=a := by
  rw [←innerHom_mul,mul_inv_cancel,innerHom_one]
lemma completed_expand_pure_inverse
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) ((completedPureAction v _ _).symm f)=
      innerHom (completedPureUnit v Ω hΩ p)⁻¹ (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  have H:=completed_expand_pure v Ω hΩ k p hq ((completedPureAction v _ _).symm f)
  rw [RingEquiv.apply_symm_apply] at H
  have HH:=congrArg (innerHom (completedPureUnit v Ω hΩ p)⁻¹) H
  rw [innerHom_inv_cancel] at HH
  exact HH.symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1)

variable (hδ : δ p=0)
lemma map_innerHom {A B : Type*} [Ring A] [Ring B] (F : A →+* B) (u : Aˣ) (x : A) :
    F (innerHom u x)=innerHom (Units.map F u) (F x) := by
  simp [innerHom]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureComparisonIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
lemma laurent_shiftedElementary_zero : shiftedElementary LaurentRay.vUnit 0=
    elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)) := by
  rw [shiftedElementary_zero,←zpow_neg_one, LaurentRay.vUnit_zpow,LaurentRay.vUnit_zpow]
  rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationRegradeCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)
variable (pc : I) (pos : Bool)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutationRegradeCompatibilityRing
local instance mutationRegradeCompatibilityAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationRegradeCompatibilityAddGroup_r4ae8d5_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
omit [DecidableEq I] in
include hcoord in
lemma completed_full_homogeneous (f : CompletedPositive v Ω C) :
    FullHomogeneous v Ω (rootOrder coord) f.val := by
  intro n m hm
  exact rootOrder_eq C coord hcoord (by by_contra hh; exact hm (f.property.2 n m hh))

include hcoord in
lemma fiberCompletion_nonp_bound (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    RegradeBound v Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val := by
  intro n m hm
  have hr : HasRootDegree C n m:=by by_contra hh; exact hm (f.property.2 n m hh)
  have hnp:=nonpDegree_root_nonneg C coord hcoord pc hr
  have H:=fiber_full_degree_bound Ω C coord hcoord pc pos hr (hf n m hm)
  refine ⟨hnp,?_⟩
  rw [←Int.toNat_of_nonneg hnp] at H
  exact_mod_cast H

include hcoord in
lemma mutationCompletion_read_full (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (n : ℕ) (m : M) (hm : HasRootDegree C n m) :
    coeff (mutationNewOrder Ω C coord pc pos m).toNat
      (mutationCompletion Ω hΩ C coord pc pos v f.val)
      (mutationLinearPiece Ω C pc pos m)=coeff n f.val m := by
  rw [mutationCompletion,coeff_map,mutationTorusPush_read]
  exact regrade_read v Ω _ _ (rootOrder coord)
    (mutationCompletion_bound Ω hΩ C coord hcoord pc pos v f hf)
    (completed_full_homogeneous v Ω C coord hcoord f) n m (rootOrder_eq C coord hcoord hm)

include hcoord in
lemma mutationCompletion_nonp_bound (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    RegradeBound v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos v f.val) := by
  intro d m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read] at hm
  have hd : d=(mutationNewOrder Ω C coord pc pos a).toNat:=by
    by_contra hh
    exact hm (ite_eq_right hh)
  rw [ite_eq_left hd] at hm
  obtain ⟨n,hn,hval⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  have hr : HasRootDegree C n a:=by by_contra hh; exact hval (f.property.2 n a hh)
  have hb:=hf n a hval
  obtain ⟨d',hr',hde⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos hr hb
  have ho:=mutationNewOrder_of_root Ω C coord hcoord pc pos hr'
  rw [ho,Int.toNat_natCast] at hd
  subst d'
  have hu:=fiberUpper_degree_bound Ω C coord hcoord pc pos hr
  have hk : 0 ≤ coord a pc:=by
    obtain ⟨b,hb,hbc,he⟩:=root_coordinates C coord hcoord hr
    rw [hbc]
    exact Int.natCast_nonneg _
  have hnp:=nonpDegree_root_nonneg C coord hcoord pc hr
  have H : (d:ℤ)≤((mutationSize Ω C pc+1:ℕ):ℤ)*nonpDegree coord pc a:=by
    push_cast
    nlinarith
  rw [mutated_nonpDegree Ω C coord hcoord pc pos a]
  refine ⟨hnp,?_⟩
  rw [←Int.toNat_of_nonneg hnp] at H
  exact_mod_cast H

include hcoord in
theorem mutation_regrade_compatibility (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    PowerSeries.map (mutationTorusPush Ω hΩ C pc pos v)
      (regrade v Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val)=
    regrade v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos v f.val) := by
  classical
  apply PowerSeries.ext
  intro D
  ext m
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [coeff_map,mutationTorusPush_read]
  by_cases hD : D=(nonpDegree coord pc a).toNat
  · subst D
    by_cases ha : ∃n,coeff n f.val a≠0
    · obtain ⟨n,hn⟩:=ha
      have hr : HasRootDegree C n a:=by by_contra hh; exact hn (f.property.2 n a hh)
      obtain ⟨d,hd,hde⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos hr (hf n a hn)
      have ho:=mutationNewOrder_of_root Ω C coord hcoord pc pos hd
      rw [regrade_read v Ω _ _ (rootOrder coord)
        (fiberCompletion_nonp_bound v Ω C coord hcoord pc pos f hf)
        (completed_full_homogeneous v Ω C coord hcoord f) n a (rootOrder_eq C coord hcoord hr)]
      rw [←mutated_nonpDegree Ω C coord hcoord pc pos a]
      rw [regrade_read v Ω _ _ (rootOrder (mutatedCoordinates Ω C coord pc))
        (mutationCompletion_nonp_bound v Ω hΩ C coord hcoord pc pos f hf)
        (completed_full_homogeneous v Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
          (mutatedCoordinates_retraction Ω C coord hcoord pc)
          (mutationCompletedPositive Ω hΩ C coord hcoord pc pos v f hf)) d _
        (rootOrder_eq (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
          (mutatedCoordinates_retraction Ω C coord hcoord pc) hd)]
      have H:=mutationCompletion_read_full v Ω hΩ C coord hcoord pc pos f hf n a hr
      rw [ho,Int.toNat_natCast] at H
      exact H.symm
    · push Not at ha
      simp only [regrade_coeff_eval,mutated_nonpDegree Ω C coord hcoord pc pos a]
      rw [Finset.sum_eq_zero (fun n hn=>ha n)]
      symm
      apply Finset.sum_eq_zero
      intro d hd
      rw [mutationCompletion_coeff_read]
      split_ifs
      · exact Finset.sum_eq_zero (fun n hn=>ha n)
      · rfl
  · simp only [regrade_coeff_eval,mutated_nonpDegree Ω C coord hcoord pc pos a,ite_eq_right hD]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPathAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
lemma comparisonWordAction_append {K M : Type*} [Field K] [AddCommGroup M]
    (u : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
    (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
    (l l' : List (ComparisonCrossing u Ω δ k B))
    (f : PowerSeries (FiberTorus u (complementOmega k Ω) (complementAlpha k p Ω))) :
    comparisonWordAction u Ω hΩ δ k p hp B (l++l') f=
    comparisonWordAction u Ω hΩ δ k p hp B l (comparisonWordAction u Ω hΩ δ k p hp B l' f) := by
  simp only [comparisonWordAction,List.foldr_append]

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedCutAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)

lemma completed_cut_identity (f : PowerSeries (FiberTorus v Ω α)) :
    completedShearAction v Ω α (completedPureAction v Ω α f)=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f := by
  apply PowerSeries.ext
  intro D
  change coeff D (PowerSeries.map (shearActionHom v Ω α)
    (PowerSeries.map (pureActionHom v Ω α) f))=_
  simp only [coeff_map]
  exact congrArg (fun F : FiberTorus v Ω α →+* FiberTorus v Ω α=>F (coeff D f))
    (rational_cut_identity v Ω α)

lemma completedOppositeInverseAction_eq (f : PowerSeries (FiberTorus v Ω α)) :
    completedOppositeInverseAction v Ω α f=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f :=
  completed_cut_identity v Ω α f

include v in
lemma completedShearAction_embed (hΩ : ∀m,Ω m m=0) (k : M →+ ℤ) (p : M) (hp : k p=1)
    (f : PowerSeries (Torus v Ω)) :
    completedShearAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (PowerSeries.map (embed v Ω hΩ k p hp) f)=
    PowerSeries.map (embed v Ω hΩ k p hp)
      (PowerSeries.map (Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p)) f) := by
  apply PowerSeries.ext
  intro D
  change coeff D (PowerSeries.map (shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω))
    (PowerSeries.map (embed v Ω hΩ k p hp) f))=_
  simp only [coeff_map]
  exact shearAction_embed v Ω hΩ k p hp (coeff D f)
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)

lemma mutationSideAction_cut_reverse (f : PowerSeries (FiberTorus v Ω α)) :
    mutationSideAction v Ω α true ((completedPureAction v Ω α).symm
      ((mutationSideAction v Ω α false).symm f))=
      (completedOppositeInverseAction v Ω α).symm f := by
  rfl

end

end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationLaurentTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [Fintype I] in
lemma mutationSideAction_embed [Fintype I] (pos : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
      (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc)) f)=
    PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc))
      (PowerSeries.map (mutationTorusEquiv LaurentRay.vUnit Ω hΩ C pc pos).toRingHom f) := by
  cases pos
  · exact completedShearAction_embed LaurentRay.vUnit Ω hΩ _ _ _ f
  · simp only [mutationSideAction, ite_true, if_true, RingEquiv.refl_apply]
    apply PowerSeries.ext
    intro D
    simp only [coeff_map]
    congr 1
    change (coeff (R := Torus LaurentRay.vUnit Ω) D f)=Finsupp.mapDomain id (coeff (R := Torus LaurentRay.vUnit Ω) D f)
    exact (Finsupp.mapDomain_id).symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteFiberInfinity
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma expandInfinity_centeredScalar (n a : ℤ) (b : K) :
    expandInfinity (RatFunc.C b*centeredScalar v n a)=
      HahnSeries.single (-n) (b*(↑(v^(-n*a)):K)) := by
  rw [centeredScalar,←mul_assoc,←map_mul,map_mul,expandInfinity_constant,expandInfinity_X_zpow]
  simp [HahnSeries.C]

lemma readFiberInfinity_monomial (m n : M) (a : K) :
    readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp (Torus.monomial v Ω n a))=
      (Torus.monomial v Ω n a) m := by
  classical
  rw [embedAdd_monomial]
  change (expandInfinity ((Finsupp.single (off k p hp n)
    (RatFunc.C a*centeredScalar v (k n) (complementAlpha k p Ω (off k p hp n))))
    (off k p hp m))).coeff (-k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=Finsupp.single n a m
  by_cases ho : off k p hp n=off k p hp m
  · rw [Finsupp.single_apply,ite_eq_left ho,expandInfinity_centeredScalar]
    by_cases hk : k n=k m
    · have hn : n=m:=split_injective k p hp hk ho
      subst n
      rw [HahnSeries.coeff_single,ite_eq_left rfl,Finsupp.single_eq_same]
      rw [mul_assoc,←Units.val_mul,←zpow_add]
      simp
    · have hn : n≠m:=fun h=>hk (congrArg k h)
      simp [Ne.symm hk,Finsupp.single_eq_of_ne (Ne.symm hn)]
  · have hn : n≠m:=fun h=>ho (congrArg (off k p hp) h)
    rw [Finsupp.single_apply,ite_eq_right ho]
    simp [Finsupp.single_eq_of_ne (Ne.symm hn)]
lemma readFiberInfinity_embedAdd (f : Torus v Ω) (m : M) :
    readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp f)=f m := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp [map_add,hf,hg]
  | single n a=>exact readFiberInfinity_monomial v Ω k p hp m n a
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_1
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_1_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_1_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
theorem mutation_rational_compatibility (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val)=
    rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val) := by
  unfold rationalRegrade
  rw [mutationSideAction_embed Ω hΩ C coord hcoord pc]
  change PowerSeries.map _ (PowerSeries.map (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit) _)=_
  rw [mutation_regrade_compatibility LaurentRay.vUnit Ω hΩ C coord hcoord pc pos f hf]

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationOrientedCompatibility
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] (v : Rˣ) (Ω : M →+ M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_3
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorus_4
local instance instAddGroupTorus_6_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma inverse_support_addSubmonoid (P : AddSubmonoid M) (f : PowerSeries (Torus v Ω))
    (hf : ∀n m,coeff n f m≠0 → m∈P) :
    ∀n m,coeff n (invOfUnit f 1) m≠0 → m∈P := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro m hm
    by_cases hn : n=0
    · subst n
      rw [coeff_invOfUnit,ite_eq_left rfl] at hm
      have hm0 : m=0:=by
        by_contra hh
        apply hm
        change Finsupp.single 0 (1:R) m=0
        exact Finsupp.single_eq_of_ne hh
      exact hm0 ▸ P.zero_mem
    · rw [coeff_invOfUnit,ite_eq_right hn] at hm
      simp only [inv_one,Units.val_one] at hm
      rw [torus_neg_one_mul] at hm
      change -(∑ab∈Finset.HasAntidiagonal.antidiagonal n,
        if ab.2<n then coeff ab.1 f*coeff ab.2 (invOfUnit f 1) else 0) m≠0 at hm
      have HH:=neg_ne_zero.mp hm
      rw [nonp_torus_eval_sum] at HH
      obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero HH
      have hb : ab.2<n:=by by_contra hh; simp [hh] at hz
      rw [ite_eq_left hb] at hz
      obtain ⟨a,b,ha,hb',he⟩:=torus_product_nonzero v Ω _ _ m hz
      exact he ▸ P.add_mem (hf ab.1 a ha) (ih ab.2 hb b hb')
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_2
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_2_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_2_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
theorem mutation_rational_oriented_compatibility (b : Bool) (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1)
        (orientPowerSeries b f.val))=
    rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b f.val)) := by
  let g : CompletedPositive LaurentRay.vUnit Ω C:=⟨orientPowerSeries b f.val,
    orientPowerSeries_constant b f.val f.property.1,orientPowerSeries_graded Ω C b f.val f.property.2⟩
  have hg : ∀n m,coeff n g.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos):=by
    cases b
    · exact inverse_support_addSubmonoid LaurentRay.vUnit Ω _ f.val hf
    · exact hf
  exact mutation_rational_compatibility Ω hΩ C coord hcoord pc pos g hg

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AffineCutTelescoping
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section

lemma sides_eq_of_ne (u v t : ℝ) (h : u+t*v≠0) :
    beforeSide u v t=decide (0<u+t*v) ∧
    afterSide u v t=decide (0<u+t*v) := by
  simp [beforeSide,afterSide,h]

lemma sides_at_zero (u v t : ℝ) (h : u+t*v=0) :
    beforeSide u v t=decide (v<0) ∧
    afterSide u v t=decide (0<v) := by
  simp [beforeSide,afterSide,h]

lemma gap_sides (u v lo hi : ℝ) (h : lo<hi) (hne : u≠0 ∨ v≠0)
    (hz : ∀t,lo<t → t<hi → u+t*v≠0) :
    afterSide u v lo=beforeSide u v hi := by
  have hstraddle : ¬(u+lo*v<0 ∧ 0<u+hi*v) := by
    rintro ⟨hl,hh⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc h.le
      (show ContinuousOn (fun t : ℝ => u+t*v) (Set.Icc lo hi) by fun_prop)
      (show (0:ℝ)∈Set.Icc (u+lo*v) (u+hi*v) from ⟨hl.le,hh.le⟩)
    have hl' : lo<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
    have hh' : t<hi := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
    exact hz t hl' hh' he
  have hstraddle' : ¬(u+hi*v<0 ∧ 0<u+lo*v) := by
    rintro ⟨hh,hl⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' h.le
      (show ContinuousOn (fun t : ℝ => u+t*v) (Set.Icc lo hi) by fun_prop)
      (show (0:ℝ)∈Set.Icc (u+hi*v) (u+lo*v) from ⟨hh.le,hl.le⟩)
    have hl' : lo<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
    have hh' : t<hi := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
    exact hz t hl' hh' he
  unfold afterSide beforeSide
  apply Bool.decide_congr
  rcases lt_trichotomy v 0 with hv | hv | hv
  · have hm : u+hi*v<u+lo*v := by nlinarith
    constructor
    · rintro (hl | ⟨hl,hv'⟩)
      · by_cases hh : 0<u+hi*v
        · exact Or.inl hh
        · exact Or.inr ⟨le_antisymm (le_of_not_gt hh)
            (not_lt.mp (fun H=>hstraddle' ⟨H,hl⟩)),hv⟩
      · linarith
    · rintro (hh | ⟨hh,_⟩) <;> exact Or.inl (by linarith)
  · subst v
    have hu : u≠0 := hne.resolve_right (by simp)
    simp
  · have hm : u+lo*v<u+hi*v := by nlinarith
    constructor
    · rintro (hl | ⟨hl,_⟩) <;> exact Or.inl (by linarith)
    · rintro (hh | ⟨hh,hv'⟩)
      · by_cases hl : 0<u+lo*v
        · exact Or.inl hl
        · exact Or.inr ⟨le_antisymm (le_of_not_gt hl)
            (not_lt.mp (fun H=>hstraddle ⟨H,hh⟩)),hv⟩
      · linarith

theorem telescope {A B : Type*} (u v : ℝ) (hne : u≠0 ∨ v≠0)
    (old : ℝ → A → A) (new : ℝ → B → B) (chart : Bool → A → B)
    (l : List ℝ) (hsort : l.Pairwise (· > ·)) (lo hi : ℝ) (hlohi : lo<hi)
    (hmem : ∀t∈l,lo<t ∧ t<hi)
    (hcut : ∀t,lo<t → t<hi → u+t*v=0 → t∈l)
    (hlocal : ∀t∈l,∀x,new t (chart (beforeSide u v t) x)=
      chart (afterSide u v t) (old t x)) (x : A) :
    l.foldr new (chart (afterSide u v lo) x)=
      chart (beforeSide u v hi) (l.foldr old x) := by
  induction l generalizing lo hi with
  | nil =>
    simp only [List.foldr_nil]
    rw [gap_sides u v lo hi hlohi hne]
    intro t hlt hth ht
    exact List.not_mem_nil (hcut t hlt hth ht)
  | cons a l ih =>
    obtain ⟨has,hsort⟩:=List.pairwise_cons.mp hsort
    obtain ⟨hla,hah⟩:=hmem a (by simp)
    have hlmem : ∀t∈l,lo<t ∧ t<a := by
      intro t ht
      exact ⟨(hmem t (by simp [ht])).1,has t ht⟩
    have hlcut : ∀t,lo<t → t<a → u+t*v=0 → t∈l := by
      intro t hlt hta ht
      have H:=hcut t hlt (hta.trans hah) ht
      rcases List.mem_cons.mp H with rfl | H
      · exact False.elim (lt_irrefl _ hta)
      · exact H
    have hg : afterSide u v a=beforeSide u v hi := by
      apply gap_sides u v a hi hah hne
      intro t hat hth ht
      have H:=hcut t (hla.trans hat) hth ht
      rcases List.mem_cons.mp H with rfl | H
      · exact lt_irrefl _ hat
      · exact (lt_asymm hat (has t H))
    simp only [List.foldr_cons]
    rw [ih hsort lo a hla hlmem hlcut (fun t ht=>hlocal t (by simp [ht])),
      hlocal a (by simp),hg]

lemma sort_strict (S : Finset ℝ) : (S.sort (· ≥ ·)).Pairwise (· > ·) := by
  have hn : (S.sort (· ≥ ·)).Pairwise (· ≠ ·) := S.sort_nodup _
  exact ((S.pairwise_sort (· ≥ ·)).and hn).imp (fun h=>lt_of_le_of_ne h.1 (Ne.symm h.2))

theorem telescope_sort {A B : Type*} (u v : ℝ) (hne : u≠0 ∨ v≠0)
    (old : ℝ → A → A) (new : ℝ → B → B) (chart : Bool → A → B)
    (S : Finset ℝ) (lo hi : ℝ) (hlohi : lo<hi)
    (hmem : ∀t∈S,lo<t ∧ t<hi)
    (hcut : ∀t,lo<t → t<hi → u+t*v=0 → t∈S)
    (hlocal : ∀t∈S,∀x,new t (chart (beforeSide u v t) x)=
      chart (afterSide u v t) (old t x)) (x : A) :
    (S.sort (· ≥ ·)).foldr new (chart (afterSide u v lo) x)=
      chart (beforeSide u v hi) ((S.sort (· ≥ ·)).foldr old x) := by
  exact telescope u v hne old new chart (S.sort (· ≥ ·)) (sort_strict S) lo hi hlohi
    (by simpa only [Finset.mem_sort] using hmem)
    (by simpa only [Finset.mem_sort] using hcut)
    (by simpa only [Finset.mem_sort] using hlocal) x
end
end ElementaryPositivity.AffineCut

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureCutTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α β : M →+ ℤ) (hβ : ∀m,β m= -α m)

lemma fiberReciprocal_oppositeInverse (f : FiberTorus v Ω α) :
    fiberReciprocal v Ω α β hβ (oppositeInverseActionHom v Ω α f)=
      pureActionInvHom v Ω β (fiberReciprocal v Ω α β hβ f) := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change fiberReciprocalAdd v Ω α β (FiberTorus.gaugeAdd v Ω α _
      (FiberTorus.monomial v Ω α m a))=
      FiberTorus.gaugeAdd v Ω β _ (fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a))
    rw [FiberTorus.gaugeAdd_monomial,fiberReciprocalAdd_monomial,
      fiberReciprocalAdd_monomial,FiberTorus.gaugeAdd_monomial]
    congr 1
    rw [map_mul,hβ]
    congr 1
    simp only [oppositeInverseRatio,Units.val_inv_eq_inv_val,reciprocalUnit_val,map_inv₀]
    have H:=congrArg (fun F : RatFunc K →+* RatFunc K=>F (↑(pureRatio v (-α m)):RatFunc K))
      reciprocal_involutive
    change reciprocal (reciprocal (↑(pureRatio v (-α m)):RatFunc K))=_ at H
    rw [H]
    rfl

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInfinityCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_10
local instance instNonUnitalSemiringTorus_10_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_10_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma completed_expand_opposite_inverse
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (completedOppositeInverseAction v _ _ f)=
    innerHom (completedPureUnit v Ω hΩ (-p))⁻¹
      (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f) := by
  calc
    _=PowerSeries.map (expandFiber v Ω hΩ k (-p))
        ((completedPureAction v (complementOmega k Ω) (complementAlpha k (-p) Ω)).symm
          (PowerSeries.map (reciprocalFiber v Ω k p) f)) := by
      rw [completedOppositeInverseAction_eq]
      apply PowerSeries.ext
      intro d
      change expandFiber v Ω hΩ k (-p)
        (reciprocalFiber v Ω k p (oppositeInverseActionHom v _ _ (coeff d f)))=
        expandFiber v Ω hΩ k (-p)
          (pureActionInvHom v _ _ (reciprocalFiber v Ω k p (coeff d f)))
      exact congrArg (expandFiber v Ω hΩ k (-p))
        (fiberReciprocal_oppositeInverse v (complementOmega k Ω) (complementAlpha k p Ω)
          (complementAlpha k (-p) Ω) (complementAlpha_neg_p Ω k p) (coeff d f))
    _=innerHom (completedPureUnit v Ω hΩ (-p))⁻¹
        (PowerSeries.map (expandFiber v Ω hΩ k (-p))
          (PowerSeries.map (reciprocalFiber v Ω k p) f)) :=
      completed_expand_pure_inverse v Ω hΩ k (-p) hq _
    _=_ := by
      congr 1
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_InfinityExpansionFaithful
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_11
local instance instNonUnitalSemiringTorus_11_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_11_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma expandFiberInfinity_monomial_coeff (l : k.ker) (a : RatFunc K) (n : ℤ) :
    (expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=
      Torus.monomial v Ω (n • (-p)+(l:M)) ((expandInfinity a).coeff n*(↑(v^(n*Ω (-p) l)):K)) := by
  change (expandFiber v Ω hΩ k (-p) (fiberReciprocalAdd v (complementOmega k Ω)
    (complementAlpha k p Ω) (complementAlpha k (-p) Ω) (FiberTorus.monomial v _ _ l a))).coeff n=_
  rw [fiberReciprocalAdd_monomial,expandFiber_monomial_coeff]
  rfl

lemma expandFiberInfinity_read_monomial (m : M) (l : k.ker) (a : RatFunc K) :
    ((expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff (-k m)) m=
      readFiberInfinity v Ω k p hp m (FiberTorus.monomial v _ _ l a) := by
  classical
  rw [expandFiberInfinity_monomial_coeff]
  simp only [neg_smul,smul_neg,neg_neg,map_neg,AddMonoidHom.neg_apply,neg_mul_neg]
  change Finsupp.single (k m • p+(l:M))
      ((expandInfinity a).coeff (-k m)*(↑(v^(k m*Ω p l)):K)) m=
    (expandInfinity ((Finsupp.single l a) (off k p hp m))).coeff (-k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  by_cases H : l=off k p hp m
  · subst l
    rw [split_sum k p hp,Finsupp.single_eq_same,Finsupp.single_eq_same]
    rfl
  · have hm : k m • p+(l:M)≠m:=by
      intro hh
      have HO:=congrArg (off k p hp) hh
      simp only [map_add,map_zsmul,off_p,smul_zero,off_complement,zero_add] at HO
      exact H HO
    rw [Finsupp.single_eq_of_ne (Ne.symm hm),Finsupp.single_eq_of_ne (Ne.symm H),map_zero,
      HahnSeries.coeff_zero,zero_mul]
lemma expandFiberInfinity_read (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) (m : M) :
    ((expandFiberInfinity v Ω hΩ k p f).coeff (-k m)) m=readFiberInfinity v Ω k p hp m f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [_root_.map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
  | single l a=>exact expandFiberInfinity_read_monomial v Ω hΩ k p hp m l a

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_InfinityUnitAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {A B : Type*} [Ring A] [Ring B]

lemma innerHom_foldr (l : List Bˣ) (x : B) :
    l.foldr (fun u y=>innerHom u y) x=innerHom l.prod x := by
  induction l with
  | nil=>simp only [List.foldr_nil,List.prod_nil,innerHom_one]
  | cons a l ih=>simp only [List.foldr_cons,List.prod_cons,ih,innerHom_mul]

lemma mapped_unit_square (F : A →+* B) (u : Aˣ) (w : Bˣ)
    (h : F u.val=w.val) (x : A) : innerHom w (F x)=F (innerHom u x) := by
  have H : Units.map F u=w := Units.ext h
  rw [map_innerHom,H]

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InfinityLaurentFinite
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.infinityLaurentFiniteRing
local instance infinityLaurentFiniteAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
include hp in
lemma expandFiberInfinity_off_diagonal
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))
    (z : ℤ) (m : M) (h : z≠-k m) :
    ((expandFiberInfinity v Ω hΩ k p f).coeff z) m=0 := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg,add_zero]
  | single l a=>
    change ((expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff z) m=0
    rw [expandFiberInfinity_monomial_coeff v Ω hΩ k p l a z]
    apply Finsupp.single_eq_of_ne
    intro hm
    apply h
    have H:=congrArg k hm
    have hl : k (l:M)=0 := l.property
    simp only [map_add,map_zsmul,map_neg,hp,hl,smul_eq_mul,add_zero,mul_neg,mul_one] at H
    omega

lemma expandFiberInfinity_embed_coeff (f : Torus v Ω) (z : ℤ) (m : M) :
    ((expandFiberInfinity v Ω hΩ k p (embed v Ω hΩ k p hp f)).coeff z) m=
      if z=-k m then f m else 0 := by
  by_cases hz : z=-k m
  · rw [ite_eq_left hz,hz,expandFiberInfinity_read v Ω hΩ k p hp]
    exact readFiberInfinity_embedAdd v Ω k p hp f m
  · rw [ite_eq_right hz]
    exact expandFiberInfinity_off_diagonal v Ω hΩ k p hp _ z m hz

lemma expandInfinity_rationalRegrade (δ : M →+ ℤ) (B D : ℕ)
    (f : PowerSeries (Torus v Ω)) (hf : LaurentBounded v Ω δ (-k) B f)
    (hg : RegradeBound v Ω δ D f) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (rationalRegrade v Ω hΩ k p hp δ D f)=laurentRegrade v Ω δ (-k) B f hf := by
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  ext m
  rw [coeff_map,rationalRegrade,coeff_map,expandFiberInfinity_embed_coeff,
    laurentRegrade_finite_read v Ω δ (-k) B D hf hg]
  rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationInfinityAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRat
local instance instAddCommMonoidTorusLaurentSeriesRat_r4ae8d5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRat_4_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma infinityCompletedUnit_mul
    (F G H : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : H.val=F.val*G.val) :
    infinityCompletedUnit Ω C coord hcoord pc v H=
      infinityCompletedUnit Ω C coord hcoord pc v F*
      infinityCompletedUnit Ω C coord hcoord pc v G := by
  apply Units.ext
  change laurentRegrade v Ω _ _ _ H.val _=_
  have Hsub : (completedInfinityUnit Ω C coord hcoord pc v H).val=
      (completedInfinityUnit Ω C coord hcoord pc v F).val*
      (completedInfinityUnit Ω C coord hcoord pc v G).val := Subtype.ext h
  exact congrArg (laurentRegradeHom v Ω _ _ _) Hsub |>.trans (map_mul _ _ _)

lemma infinityCompletedUnit_one (F : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : F.val=1) : infinityCompletedUnit Ω C coord hcoord pc v F=1 := by
  apply Units.ext
  change laurentRegrade v Ω _ _ _ F.val _=1
  have Hsub : (completedInfinityUnit Ω C coord hcoord pc v F).val=1:=Subtype.ext h
  exact congrArg (laurentRegradeHom v Ω _ _ _) Hsub |>.trans (map_one _)

lemma infinityCompletedUnit_inverse
    (F G : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : G.val=invOfUnit F.val 1) :
    infinityCompletedUnit Ω C coord hcoord pc v G=
      (infinityCompletedUnit Ω C coord hcoord pc v F)⁻¹ := by
  apply Units.ext
  change mutatedLaurent Ω C coord hcoord pc v G=
    mutatedLaurent Ω C coord hcoord pc v (completedInverse v Ω (mutatedRoots Ω C pc) F)
  exact congrArg _ (Subtype.ext h)

lemma infinityCompletedUnit_pure (hΩ : ∀m,Ω m m=0)
    (F : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : F.val=raySeries v Ω (-simpleRoot C pc) (shiftedElementary v 0)) :
    infinityCompletedUnit Ω C coord hcoord pc v F=
      completedPureUnit v Ω hΩ (-simpleRoot C pc) := by
  have hd : nonpDegree (mutatedCoordinates Ω C coord pc) pc (-simpleRoot C pc)=0 := by
    rw [←mutatedRoot_p Ω C pc]
    exact nonpDegree_simple_self (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) pc
  have hk : (-pureDegree coord pc) (-simpleRoot C pc)=1 := by
    simp only [AddMonoidHom.neg_apply,map_neg,neg_neg,pureDegree_simple_self C coord hcoord pc]
  apply Units.ext
  change laurentRegrade v Ω _ _ _ F.val _=PowerSeries.C _
  have H:=laurentRegrade_pure v Ω
    (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (-pureDegree coord pc)
    (mutationSize Ω C pc) (-simpleRoot C pc) hd hk (shiftedElementary v 0)
  calc
    _ = PowerSeries.C (HahnSeries.ofPowerSeries ℤ (Torus v Ω)
        (raySeries v Ω (-simpleRoot C pc) (shiftedElementary v 0))) := by
      convert H using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
    _ = _ := by
      congr 1
      exact (purePower_eq v Ω hΩ (-simpleRoot C pc) (shiftedElementary v 0)).symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_12
local instance instNonUnitalSemiringTorus_12_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_12_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma completed_expand_opposite
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      ((completedOppositeInverseAction v _ _).symm f)=
    innerHom (completedPureUnit v Ω hΩ (-p))
      (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f) := by
  have H:=completed_expand_opposite_inverse v Ω hΩ k p hq
    ((completedOppositeInverseAction v _ _).symm f)
  rw [RingEquiv.apply_symm_apply] at H
  have HH:=congrArg (innerHom (completedPureUnit v Ω hΩ (-p))) H
  rw [innerHom_cancel_inv] at HH
  exact HH.symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityCutCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_13
local instance instNonUnitalSemiringTorus_13_r4ae8d5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_13_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma infinitySide_cut (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    innerHom (completedPureUnit v Ω hΩ (-p))⁻¹ (infinitySideHom v Ω hΩ k p true f)=
      infinitySideHom v Ω hΩ k p false (completedPureAction v _ _ f) := by
  change innerHom _ (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f)=_
  rw [←completed_expand_opposite_inverse v Ω hΩ k p hq]
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    (completedOppositeInverseAction v _ _ f)=
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (mutationSideAction v _ _ false (completedPureAction v _ _ f))
  congr 1

lemma infinitySide_cut_reverse (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    innerHom (completedPureUnit v Ω hΩ (-p))
        (infinitySideHom v Ω hΩ k p false f)=
      infinitySideHom v Ω hΩ k p true ((completedPureAction v _ _).symm f) := by
  rw [show infinitySideHom v Ω hΩ k p false f=
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (mutationSideAction v _ _ false f) from rfl]
  rw [←completed_expand_opposite v Ω hΩ k p hq]
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    ((completedOppositeInverseAction v _ _).symm
      (mutationSideAction v _ _ false f))=_
  congr 1
  have H:=mutationSideAction_cut_reverse v (complementOmega k Ω) (complementAlpha k p Ω)
    (mutationSideAction v _ _ false f)
  rw [RingEquiv.symm_apply_apply] at H
  exact H.symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_4
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_4_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_4_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_r4ae8d5_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_r4ae8d5_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
lemma mutation_infinity_oriented (pos b : Bool) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n F.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (G : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc))
    (hG : G.val=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b F.val)) :
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1)
        (orientPowerSeries b F.val)) = mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit G := by
  let f : CompletedPositive LaurentRay.vUnit Ω C:=⟨orientPowerSeries b F.val,
    orientPowerSeries_constant b F.val F.property.1,orientPowerSeries_graded Ω C b F.val F.property.2⟩
  have hg : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos):=by
    cases b
    · exact inverse_support_addSubmonoid LaurentRay.vUnit Ω _ F.val hf
    · exact hf
  have hb : RegradeBound LaurentRay.vUnit Ω
      (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1) G.val := by
    rw [hG]
    exact mutationCompletion_nonp_bound LaurentRay.vUnit Ω hΩ C coord hcoord pc pos f hg
  have HT:=congrArg (PowerSeries.map (expandFiberInfinity LaurentRay.vUnit Ω hΩ
      (pureDegree coord pc) (simpleRoot C pc)))
    (mutation_rational_oriented_compatibility Ω hΩ C coord hcoord pc pos b F hf)
  have HG:=congrArg (fun t : PowerSeries (Torus LaurentRay.vUnit Ω) =>
    PowerSeries.map (expandFiberInfinity LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc))
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
        (mutationSize Ω C pc+1) t)) hG.symm
  exact HT.trans (HG.trans (expandInfinity_rationalRegrade LaurentRay.vUnit Ω hΩ
    (pureDegree coord pc) (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) _ _ _ G.val
    (mutated_series_laurentBounded Ω C coord hcoord pc LaurentRay.vUnit G.property.2) hb))
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_5
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_5_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_5_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutation_infinity_oriented_square (pos b : Bool) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n F.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (hbf : RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) F.val)
    (hbi : RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) (invOfUnit F.val 1))
    (G : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc))
    (hG : G.val=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b F.val))
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos
      (comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (orientedBounded LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
          (mutationSize Ω C pc+1) (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc F) hbf hbi b) x) := by
  have hh:=mutation_infinity_oriented Ω hΩ C coord hcoord pc pos b F hf G hG
  cases b
  · exact mapped_unit_square
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos)
      (boundedRationalUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc F)⁻¹ hbi hbf)
      (infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G) hh x
  · exact mapped_unit_square
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos)
      (boundedRationalUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc F) hbf hbi)
      (infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G) hh x
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.infinityLineRing
local instance infinityLineAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance infinityLineAddGroup_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualInfinityLine_nocut (a : ℝ)
    (hp : (k+a • v) (e (simpleRoot C pc))≠0)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<(k+a • v) (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<(k+a • v) (e (simpleRoot C pc))))
      (comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) x) := by
  classical
  let pos:=decide (0<(k+a • v) (e (simpleRoot C pc)))
  have hs:=cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp
  unfold actualLineLetter
  split
  · next ha=>
    simp only
    let data:=lineRayData C e he L hdeg v k H a ha
    let F:=chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)
    let G:=mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
    have hf:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    have hG : G.val=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (orientPowerSeries (decide (v (e data.root)<0)) F.val) := by
      simp only [G,mutatedLineFactorPositive,mutatedLineFactor,dite_eq_left ha,ite_eq_right hp]
      rfl
    have hbf:=simple_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    have hbi:=simple_inverse_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    exact mutation_infinity_oriented_square Ω hΩ C coord hcoord pc pos
      (decide (v (e data.root)<0)) F hf hbf hbi G hG x
  · next ha=>
    have hg : (mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a).val=1 := by
      simp only [mutatedLineFactorPositive,mutatedLineFactor,dite_eq_right ha]
    have hu:=infinityCompletedUnit_one Ω C coord hcoord pc LaurentRay.vUnit _ hg
    change innerHom _ _=infinitySideHom _ _ _ _ _ _ (innerHom _ x)
    rw [show actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a=1 from hu,
      innerHom_one]
    have h1 : boundedRationalUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _)=1 := by
      apply Units.ext
      exact rationalRegrade_one _ _ _ _ _ _ _ _
    rw [h1,innerHom_one]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.infinityLineCutRing
local instance infinityLineCutAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance infinityLineCutAddGroup_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualInfinityLine_cut_unit (a : ℝ)
    (hp : (k+a • v) (e (simpleRoot C pc))=0) :
    actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a=
      if decide (v (e (simpleRoot C pc))<0) then
        (completedPureUnit LaurentRay.vUnit Ω hΩ (-simpleRoot C pc))⁻¹
      else completedPureUnit LaurentRay.vUnit Ω hΩ (-simpleRoot C pc) := by
  classical
  have ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k :=
    ⟨1,line_cut_event C pc e L hdeg v k H a hp⟩
  let P : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
    ⟨normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc),
      normalizedSimple_constant Ω _,by
        rw [←simpleDatum_value Ω (mutatedRoots Ω C pc) pc]
        exact WallUnitDatum.graded Ω _ (fun _=>True) _ (simpleDatum_allowed _ pc)⟩
  have hP : P.val=raySeries LaurentRay.vUnit Ω (-simpleRoot C pc) (shiftedElementary LaurentRay.vUnit 0) := by
    rw [laurent_shiftedElementary_zero]
    change normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)=_
    rw [mutatedRoot_p]
    rfl
  have hU:=infinityCompletedUnit_pure Ω C coord hcoord pc LaurentRay.vUnit hΩ P hP
  let G:=mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
  have hG : G.val=orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0))) P.val := by
    simp only [G,mutatedLineFactorPositive,mutatedLineFactor,dite_eq_left ha,ite_eq_left hp,P]
  cases hb : decide (v (e (simpleRoot C pc))<0)
  · simp only [Bool.false_eq_true,ite_false, if_false]
    change infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G=_
    rw [show G=P from Subtype.ext (by simpa only [hb,Bool.not_false,orientPowerSeries,ite_true, if_true] using hG)]
    exact hU
  · simp only [ite_true, if_true]
    change infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G=_
    rw [infinityCompletedUnit_inverse Ω C coord hcoord pc LaurentRay.vUnit P G
      (by simpa only [hb,Bool.not_true,orientPowerSeries,Bool.false_eq_true,ite_false, if_false] using hG),hU]

include hdeg H in
lemma line_cut_offset_ne : k (e (simpleRoot C pc))≠0 := by
  have hr : e (simpleRoot C pc)∈realRootsThrough e C 1 := by
    exact realRoot_mem e C 1 1 le_rfl (simpleRoot C pc) (simpleRoot_degree C pc)
  apply (H 1).avoid _ hr
  rw [Submodule.span_singleton_eq_bot.mpr rfl,Submodule.mem_bot]
  intro hz
  have HH:=hdeg 1 (simpleRoot C pc) (simpleRoot_degree C pc)
  rw [hz,map_zero] at HH
  norm_num at HH

include hdeg H in
lemma line_cut_direction_ne (a : ℝ) (hp : (k+a • v) (e (simpleRoot C pc))=0) :
    v (e (simpleRoot C pc))≠0 := by
  intro hz
  have hp' : k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0:=hp
  rw [hz,mul_zero,add_zero] at hp'
  exact line_cut_offset_ne C pc e L hdeg v k H hp'
lemma actualInfinityLine_square (a : ℝ)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (AffineCut.beforeSide (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (AffineCut.afterSide (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a)
      (comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) x) := by
  classical
  by_cases hp : (k+a • v) (e (simpleRoot C pc))=0
  · have hs:=AffineCut.sides_at_zero (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a hp
    rw [hs.1,hs.2,actualInfinityLine_cut_unit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a hp]
    have ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k :=
      ⟨1,line_cut_event C pc e L hdeg v k H a hp⟩
    have hv:=line_cut_direction_ne C pc e L hdeg v k H a hp
    have hq : ∀n : ℕ,1-(↑(LaurentRay.vUnit^(-2:ℤ)):LaurentSeries ℚ)^(n+1)≠0 := by
      intro n
      rw [LaurentRay.vUnit_zpow]
      exact UnitSelections.laurent_q_not_root n
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_left hp]
    by_cases hn : v (e (simpleRoot C pc))<0
    · have hn' : ¬0<v (e (simpleRoot C pc)):=not_lt_of_ge hn.le
      simp only [hn,hn',decide_true,decide_false,ite_true, if_true,comparisonAction]
      exact infinitySide_cut LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) hq x
    · have hn' : 0<v (e (simpleRoot C pc)):=lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hv)
      simp only [hn,hn',decide_true,decide_false,Bool.false_eq_true,ite_false, if_false,comparisonAction]
      exact infinitySide_cut_reverse LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) hq x
  · have hs:=AffineCut.sides_eq_of_ne (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a hp
    rw [hs.1,hs.2]
    exact actualInfinityLine_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a hp x
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPureLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedPureLineProductRing
local instance mutatedPureLineProductAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutatedPureLineProductAddGroup_r4ae8d5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
omit [DecidableEq I] in
lemma completedProduct_val (l : List (CompletedPositive v Ω C)) :
    (completedProduct Ω C v l).val=(l.map (fun F=>F.val)).prod := by
  induction l with
  | nil=>rfl
  | cons a l ih=>exact congrArg (fun x=>a.val*x) ih

lemma infinityCompletedUnit_product (l : List (CompletedPositive v Ω (mutatedRoots Ω C pc))) :
    infinityCompletedUnit Ω C coord hcoord pc v (completedProduct Ω (mutatedRoots Ω C pc) v l)=
      (l.map (infinityCompletedUnit Ω C coord hcoord pc v)).prod := by
  induction l with
  | nil=>exact infinityCompletedUnit_one Ω C coord hcoord pc v _ rfl
  | cons a l ih=>
    rw [List.map_cons,List.prod_cons,←ih]
    exact infinityCompletedUnit_mul Ω C coord hcoord pc v _ _ _ rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.mutatedPureLineFiberRing
local instance mutatedPureLineFiberAddCommMonoid_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPureLineFiberAddGroup_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualInfinityLineProductUnit_eq (lo hi : ℝ) (N : ℕ) :
    actualInfinityLineProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N=
      infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit
        (mutatedLineProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) := by
  let l:=(intervalEventList C e v k lo hi N).map
    (mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H)
  have heq : mutatedLineProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N=
      completedProduct Ω (mutatedRoots Ω C pc) LaurentRay.vUnit l := by
    apply Subtype.ext
    rw [completedProduct_val]
    simp only [l,List.map_map,Function.comp_def]
    rfl
  rw [heq,infinityCompletedUnit_product]
  simp only [l,List.map_map,Function.comp_def]
  rfl

lemma actualInfinityLine_product_square (lo hi : ℝ) (hlohi : lo<hi)
    (hlo : lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi : hi∉lineEvents (realRootsThrough e C 1) v k) (N : ℕ) (hN : 1≤N)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityLineProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<(k+lo • v) (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<(k+hi • v) (e (simpleRoot C pc))))
      (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) x) := by
  classical
  have hl : (k+lo • v) (e (simpleRoot C pc))≠0 :=
    fun hh=>hlo (line_cut_event C pc e L hdeg v k H lo hh)
  have hh : (k+hi • v) (e (simpleRoot C pc))≠0 :=
    fun hz=>hhi (line_cut_event C pc e L hdeg v k H hi hz)
  have HT:=AffineCut.telescope_sort (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc)))
    (Or.inl (line_cut_offset_ne C pc e L hdeg v k H))
    (fun a=>comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a))
    (fun a=>innerHom (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a))
    (fun pos=>infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos)
    (intervalLineEvents C e v k lo hi N) lo hi hlohi
    (fun a ha=>(Finset.mem_filter.mp ha).2)
    (by
      intro a hla hah hz
      apply Finset.mem_filter.mpr
      exact ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
        (line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩)
    (fun a _=>actualInfinityLine_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a) x
  rw [(AffineCut.sides_eq_of_ne _ _ lo hl).2,(AffineCut.sides_eq_of_ne _ _ hi hh).1] at HT
  simpa only [actualInfinityLineProductUnit,←innerHom_foldr,List.foldr_map,
    comparisonWordAction,actualLineWord,intervalEventList,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using HT
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_6
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_6_r4ae8d5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_6_r4ae8d5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualInfinityPathProductUnit_nil (a : Module.Dual ℝ E) (N : ℕ) :
    actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg (.nil a) N=1 :=
  infinityCompletedUnit_one Ω C coord hcoord pc LaurentRay.vUnit _ rfl

lemma actualInfinityPathProductUnit_append {a : Module.Dual ℝ E} (s : GenericLineSegment C e)
    (p : GenericLinePath C e a (s.start C e)) (N : ℕ) :
    actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg (.append s p) N=
      actualInfinityLineProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
        s.direction s.offset s.generic s.lo s.hi N*
      actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N := by
  rw [actualInfinityLineProductUnit_eq]
  exact infinityCompletedUnit_mul Ω C coord hcoord pc LaurentRay.vUnit _ _ _ rfl

lemma actualInfinityPath_product_square_oai {a b : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (N : ℕ) (hN : 1≤N)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<a (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<b (e (simpleRoot C pc))))
      (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N) x) := by
  induction p with
  | nil=>rw [actualInfinityPathProductUnit_nil,innerHom_one]; rfl
  | append s p ih=>
    rw [actualInfinityPathProductUnit_append,innerHom_mul,ih]
    exact (actualInfinityLine_product_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1)
      N hN _).trans (by rw [actualPathWord,comparisonWordAction_append]; rfl)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square_oai.{u_1, u_2, u_3}
