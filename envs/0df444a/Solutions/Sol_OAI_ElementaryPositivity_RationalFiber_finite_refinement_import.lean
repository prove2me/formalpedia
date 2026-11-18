-- Prove2me | solution 1 for OAI.ElementaryPositivity.RationalFiber.finite_refinement_import
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:06.836419+00:00
-- url     : https://prove2.me/submissions/aaa7e2bd-7fbf-4ee7-8577-eb5e58d3d3c3

import Mathlib
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom012
import Definitions.Def_OAIQ368Chrom014
import Definitions.Def_OAIQ368Chrom025

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open Polynomial
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]
lemma expandZero_injective : Function.Injective (expandZero (K:=K)) := (expandZero (K:=K)).injective
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusFaithful
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
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
lemma expand_centeredScalar (n a : ℤ) (b : K) :
    expandZero (RatFunc.C b*centeredScalar v n a)=
      HahnSeries.single n (b*(↑(v^(-n*a)):K)) := by
  rw [centeredScalar,←mul_assoc,←map_mul,map_mul,expandZero_constant,expandZero_X_zpow]
  simp [HahnSeries.C]

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalReadExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma readFiber_ext {f g : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)}
    (h : ∀m,readFiber v Ω k p hp m f=readFiber v Ω k p hp m g) : f=g := by
  apply Finsupp.ext
  intro l
  apply expandZero_injective
  apply HahnSeries.ext
  funext n
  have H:=h (n • p+(l:M))
  change (expandZero (f (off k p hp (n • p+(l:M))))).coeff (k (n • p+(l:M)))*
    (↑(v^(k (n • p+(l:M))*complementAlpha k p Ω (off k p hp (n • p+(l:M))))):K)=
    (expandZero (g (off k p hp (n • p+(l:M))))).coeff (k (n • p+(l:M)))*
    (↑(v^(k (n • p+(l:M))*complementAlpha k p Ω (off k p hp (n • p+(l:M))))):K) at H
  have hl : k (l:M)=0:=l.property
  simp only [map_add,map_zsmul,off_p,smul_zero,off_complement,zero_add,hp,
    smul_eq_mul,mul_one,hl,add_zero] at H
  exact mul_right_cancel₀ (Units.ne_zero _) H
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge_monomial _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
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
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalLaurentFaithfulRing
local instance rationalLaurentFaithfulNonUnitalSemiring_r3afc47_1 : NonUnitalSemiring (Torus v Ω) :=
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
lemma expansion_embed_monomial (m : M) (a : K) :
    expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.monomial v Ω m a))=
      HahnSeries.single (k m) (Torus.monomial v Ω m a) := by
  rw [embed_monomial]
  apply HahnSeries.ext
  funext n
  rw [expandFiber_monomial_coeff,expand_centeredScalar]
  simp only [HahnSeries.coeff_single]
  by_cases H : n=k m
  · subst n
    rw [ite_eq_left rfl,ite_eq_left rfl,split_sum k p hp]
    congr 1
    change a*(↑(v^(-k m*complementAlpha k p Ω (off k p hp m))):K)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=a
    rw [mul_assoc,←Units.val_mul,←zpow_add]
    simp
  · simp [H,Torus.monomial]
lemma expandFiber_read_monomial (m : M) (l : k.ker) (a : RatFunc K) :
    ((expandFiber v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff (k m)) m=
      readFiber v Ω k p hp m (FiberTorus.monomial v _ _ l a) := by
  classical
  rw [expandFiber_monomial_coeff]
  change Finsupp.single (k m • p+(l:M))
      ((expandZero a).coeff (k m)*(↑(v^(k m*Ω p l)):K)) m=
    (expandZero ((Finsupp.single l a) (off k p hp m))).coeff (k m)*
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
lemma expandFiber_read (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) (m : M) :
    ((expandFiber v Ω hΩ k p f).coeff (k m)) m=readFiber v Ω k p hp m f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [_root_.map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
  | single l a=>exact expandFiber_read_monomial v Ω hΩ k p hp m l a
include hp in
lemma expandFiber_injective : Function.Injective (expandFiber v Ω hΩ k p) := by
  intro f g h
  apply readFiber_ext v Ω k p hp
  intro m
  rw [←expandFiber_read v Ω hΩ k p hp f m,←expandFiber_read v Ω hΩ k p hp g m,h]
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
local instance regradeFaithfulAddCommMonoid_r3afc47_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeFaithfulAddGroup_r3afc47_1 : AddGroup (Torus v Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge_monomial _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
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
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.laurentExpansionRing
local instance laurentExpansionAddCommMonoid_r3afc47_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentExpansionAddGroup_r3afc47_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance laurentExpansionNonUnitalSemiring_r3afc47_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentExpansionNonUnitalNonAssocSemiring_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma expand_embed_coeff (f : Torus v Ω) (n : ℤ) (m : M) :
    ((expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp f)).coeff n) m=
      if n=k m then f m else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>
    simp only [map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
    split_ifs <;> simp
  | single l a=>
    change ((expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.monomial v Ω l a))).coeff n) m=_
    rw [expansion_embed_monomial,HahnSeries.coeff_single]
    by_cases hl : l=m
    · subst l; split_ifs <;> rfl
    · by_cases hn : n=k l
      · rw [ite_eq_left hn]
        simp [Torus.monomial,Finsupp.single_eq_of_ne (Ne.symm hl)]
      · rw [ite_eq_right hn]
        simp [Finsupp.single_eq_of_ne (Ne.symm hl)]
lemma hahn_power_negative (f : PowerSeries (Torus v Ω)) (n : ℤ) (hn : n<0) :
    (HahnSeries.ofPowerSeries ℤ (Torus v Ω) f).coeff n=0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨a,ha⟩
  change (a:ℤ)=n at ha
  omega
variable (δ : M →+ ℤ) (B : ℕ)
lemma regrade_eval_vanish (f : PowerSeries (Torus v Ω)) (d : ℕ) (m : M)
    (hz : ∀n,PowerSeries.coeff n f m=0) : PowerSeries.coeff d (regrade v Ω δ B f) m=0 := by
  rw [regrade_coeff_eval]
  simp [hz]
lemma regrade_expand_nat {f : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ k f) (hb : RegradeBound v Ω δ B f) (d e : ℕ) (m : M) :
    ((expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp (PowerSeries.coeff d (regrade v Ω δ B f)))).coeff (e:ℤ)) m=
      PowerSeries.coeff e (PowerSeries.coeff d (biRegrade v Ω δ k f)) m := by
  rw [expand_embed_coeff,biRegrade_coeff,biHomogenize_coeff]
  by_cases hδ : 0≤δ m
  · by_cases hk : 0≤k m
    · have hd : ((δ m).toNat:ℤ)=δ m:=Int.toNat_of_nonneg hδ
      have he : ((k m).toNat:ℤ)=k m:=Int.toNat_of_nonneg hk
      by_cases hD : d=(δ m).toNat
      · by_cases hE : e=(k m).toNat
        · have Hk : (e:ℤ)=k m:=by omega
          rw [ite_eq_left Hk,ite_eq_left ⟨hD,hE⟩]
          have Hτ : FullHomogeneous v Ω (δ+k) f:=by
            intro n m hm
            exact (hf n m hm).2.2.symm
          simpa only [hD] using (regrade_read v Ω δ B (δ+k) hb Hτ (d+e) m (by
            change δ m+k m=((d+e:ℕ):ℤ)
            rw [Nat.cast_add]
            omega))
        · have Hk : (e:ℤ)≠k m:=by omega
          rw [ite_eq_right Hk,ite_eq_right (by tauto)]
      · rw [ite_eq_right (by tauto : ¬(d=(δ m).toNat ∧ e=(k m).toNat))]
        rw [regrade_coeff_eval,ite_eq_right hD]
        split_ifs <;> rfl
    · have hz : ∀j,PowerSeries.coeff j f m=0:=by
        intro j; by_contra H; exact hk (hf j m H).2.1
      rw [regrade_eval_vanish v Ω δ B f d m hz,hz]
      split_ifs <;> rfl
  · have hz : ∀j,PowerSeries.coeff j f m=0:=by
      intro j; by_contra H; exact hδ (hf j m H).1
    rw [regrade_eval_vanish v Ω δ B f d m hz,hz]
    split_ifs <;> rfl
lemma rational_old_square {f : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ k f) (hb : RegradeBound v Ω δ B f) :
    PowerSeries.map (expandFiber v Ω hΩ k p)
      (rationalRegrade v Ω hΩ k p hp δ B f)=oldLaurent v Ω δ k f := by
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext n
  apply Finsupp.ext
  intro m
  simp only [rationalRegrade,oldLaurent,PowerSeries.coeff_map]
  rcases le_or_gt 0 n with hn|hn
  · lift n to ℕ using hn with e he
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact regrade_expand_nat v Ω hΩ k p hp δ B hf hb d e m
  · rw [hahn_power_negative v Ω _ n hn,expand_embed_coeff]
    by_cases he : n=k m
    · rw [ite_eq_left he]
      apply regrade_eval_vanish
      intro j
      by_contra H
      have HH:=(hf j m H).2.1
      omega
    · rw [ite_eq_right he]
      rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

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
local instance instAddCommMonoidTorus_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ κ : M →+ ℤ) (p : M) (hδ : δ p=0) (hκ : κ p=1)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_3
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instAddCommMonoidTorus_1
local instance instAddGroupTorus_1_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_3_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_3_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
include hδ hκ in
lemma biRegrade_pure (f : PowerSeries K) :
    biRegrade v Ω δ κ (raySeries v Ω p f)=PowerSeries.C (raySeries v Ω p f) := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [biRegrade_coeff,coeff_raySeries,biHomogenize_monomial]
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one,
    Int.toNat_natCast,coeff_monomial]
  by_cases hd : d=0
  · subst d
    simp [coeff_C,coeff_raySeries]
  · simp [coeff_C,hd]
include hδ hκ in
lemma oldLaurent_pure (f : PowerSeries K) :
    oldLaurent v Ω δ κ (raySeries v Ω p f)=PowerSeries.C (purePower v Ω hΩ p f) := by
  rw [oldLaurent,biRegrade_pure v Ω δ κ p hδ hκ,PowerSeries.map_C,purePower_eq]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
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
local instance instNonUnitalSemiringTorus_4_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_4_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_5
local instance instAddCommMonoidTorus_2_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_2_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_5_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_5_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma boundedUnit_expansion (B : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hg : RegradeBound v Ω δ B u.inv.val) :
    Units.map (PowerSeries.map (expandFiber v Ω hΩ k p))
      (boundedRationalUnit v Ω hΩ δ k p hp B u hf hg)=oldUnitExpand v Ω δ k u := by
  apply Units.ext
  change PowerSeries.map (expandFiber v Ω hΩ k p)
    (rationalRegrade v Ω hΩ k p hp δ B u.val.val)=oldLaurent v Ω δ k u.val.val
  exact rational_old_square v Ω hΩ k p hp δ B u.val.property hf

variable (hδ : δ p=0)
lemma oldPureUnit_expansion :
    oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)=completedPureUnit v Ω hΩ p := by
  apply Units.ext
  exact oldLaurent_pure v Ω hΩ δ k p hδ hp _
lemma map_innerHom {A B : Type*} [Ring A] [Ring B] (F : A →+* B) (u : Aˣ) (x : A) :
    F (innerHom u x)=innerHom (Units.map F u) (F x) := by
  simp [innerHom]
lemma bounded_conjugation_expansion (B : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hg : RegradeBound v Ω δ B u.inv.val)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p)
      (innerHom (boundedRationalUnit v Ω hΩ δ k p hp B u hf hg) f)=
      innerHom (oldUnitExpand v Ω δ k u) (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  rw [map_innerHom,boundedUnit_expansion]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_6
local instance instAddCommMonoidTorus_3_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_6_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_6_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma comparison_expansion (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (c : ComparisonCrossing v Ω δ k B)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (comparisonAction v Ω hΩ δ k p hp B c f)=
      innerHom (oldUnitExpand v Ω δ k (comparisonOld v Ω hΩ δ k p hp hδ B c))
        (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  cases c with
  | bounded u hf hg=>exact bounded_conjugation_expansion v Ω hΩ δ k p hp B u hf hg f
  | pure b=>
    cases b
    · change _=innerHom (oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)⁻¹) _
      have H : oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)⁻¹=
          (completedPureUnit v Ω hΩ p)⁻¹ := by
        rw [oldUnitExpand,map_inv,←oldPureUnit_expansion v Ω hΩ δ k p hp hδ]
        rfl
      rw [H]
      exact completed_expand_pure_inverse v Ω hΩ k p hq f
    · change _=innerHom (oldUnitExpand v Ω δ k (oldPureUnit v Ω hΩ δ k p hp hδ)) _
      rw [oldPureUnit_expansion]
      exact completed_expand_pure v Ω hΩ k p hq f

lemma comparisonWord_expansion (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (l : List (ComparisonCrossing v Ω δ k B))
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (comparisonWordAction v Ω hΩ δ k p hp B l f)=
      innerHom (oldUnitExpand v Ω δ k (comparisonWordOld v Ω hΩ δ k p hp hδ B l))
        (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  induction l with
  | nil=>simp [comparisonWordAction,comparisonWordOld,oldUnitExpand,innerHom_one]
  | cons c l ih=>
    change PowerSeries.map (expandFiber v Ω hΩ k p)
      (comparisonAction v Ω hΩ δ k p hp B c (comparisonWordAction v Ω hΩ δ k p hp B l f))=_
    rw [comparison_expansion v Ω hΩ δ k p hp hδ B hq,ih]
    change _=innerHom (oldUnitExpand v Ω δ k
      (comparisonOld v Ω hΩ δ k p hp hδ B c*comparisonWordOld v Ω hΩ δ k p hp hδ B l)) _
    simp only [oldUnitExpand,map_mul,innerHom_mul]

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
namespace ElementaryPositivity.BiTruncation
open PowerSeries
variable {R : Type*} [Semiring R]
lemma Through.refl (N : ℕ) (f : PowerSeries (PowerSeries R)) : Through N f f := by
  intro d e h; rfl
lemma Through.mul {N : ℕ} {f f' g g' : PowerSeries (PowerSeries R)}
    (hf : Through N f f') (hg : Through N g g') : Through N (f*g) (f'*g') := by
  intro d e hde
  simp only [coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro kl hkl
  have H1:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have H2:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rw [hf ij.1 kl.1 (by omega),hg ij.2 kl.2 (by omega)]
lemma Through.conjugate {N : ℕ} {u w : PowerSeries (PowerSeries R)}
    (hu : Through N u 1) (hw : Through N w 1) (f : PowerSeries (PowerSeries R)) :
    Through N (u*f*w) f := by
  simpa only [one_mul,mul_one] using (hu.mul (Through.refl N f)).mul hw
end ElementaryPositivity.BiTruncation

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries BiTruncation
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.biThroughRing
local instance biThroughAddCommMonoid_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance biThroughAddGroup_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance biThroughNonUnitalSemiring_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance biThroughNonUnitalNonAssocSemiring_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma biRegrade_through {f g : PowerSeries (Torus v Ω)} (N : ℕ)
    (h : ∀n≤N,coeff n f=coeff n g) :
    Through N (biRegrade v Ω δ κ f) (biRegrade v Ω δ κ g) := by
  intro d e he
  rw [biRegrade_coeff,biRegrade_coeff,h (d+e) he]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalThroughRing
local instance rationalThroughAddCommMonoid_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma regrade_congr_through (D : ℕ) {f g : PowerSeries (Torus v Ω)}
    (he : ∀n≤B*D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (regrade v Ω δ B f)=coeff d (regrade v Ω δ B g) := by
  intro d hd
  rw [regrade_coeff,regrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [he n (by have H:=Finset.mem_range.mp hn; have HH:=Nat.mul_le_mul_left B hd; omega)]
lemma rationalRegrade_congr_through (D : ℕ) {f g : PowerSeries (Torus v Ω)}
    (he : ∀n≤B*D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (rationalRegrade v Ω hΩ k p hp δ B f)=
      coeff d (rationalRegrade v Ω hΩ k p hp δ B g) := by
  intro d hd
  simp only [rationalRegrade,coeff_map]
  rw [regrade_congr_through v Ω δ B D he d hd]
lemma oldUnit_inverse_congr (u w : (biSupportedSubring v Ω δ k)ˣ) (N : ℕ)
    (h : ∀n≤N,coeff n u.val.val=coeff n w.val.val) :
    ∀n≤N,coeff n u.inv.val=coeff n w.inv.val := by
  intro n hn
  have HE:=FormalLog.mul_coeff_congr u.inv.val (u.val.val*w.inv.val)
    u.inv.val (w.val.val*w.inv.val) n (fun _ _=>rfl) (by
      intro j hj
      exact FormalLog.mul_coeff_congr _ _ _ _ j (fun t ht=>h t (ht.trans (hj.trans hn))) (fun _ _=>rfl))
  have hu : u.inv.val*u.val.val=1:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.inv_val
  have hw : w.val.val*w.inv.val=1:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) w.val_inv
  rw [←mul_assoc,hu,one_mul,hw,mul_one] at HE
  exact HE.symm
lemma innerHom_coeff_congr {A : Type*} [Ring A] (u w : (PowerSeries A)ˣ)
    (f g : PowerSeries A) (N : ℕ)
    (hv : ∀n≤N,coeff n u.val=coeff n w.val)
    (hi : ∀n≤N,coeff n u.inv=coeff n w.inv)
    (hf : ∀n≤N,coeff n f=coeff n g) :
    coeff N (innerHom u f)=coeff N (innerHom w g) := by
  change coeff N (u.val*f*u.inv)=coeff N (w.val*g*w.inv)
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr _ _ _ _ j (fun t ht=>hv t (ht.trans hj))
      (fun t ht=>hf t (ht.trans hj))
  · exact hi
lemma comparisonAction_input_congr (c : ComparisonCrossing v Ω δ k B)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (N : ℕ) (hg : ∀n≤N,coeff n f=coeff n g) :
    coeff N (comparisonAction v Ω hΩ δ k p hp B c f)=
      coeff N (comparisonAction v Ω hΩ δ k p hp B c g) := by
  cases c with
  | bounded u hf hi=>exact innerHom_coeff_congr _ _ _ _ N (fun _ _=>rfl) (fun _ _=>rfl) hg
  | pure b=>
    cases b
    · change coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).symm.toRingHom f)=
        coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).symm.toRingHom g)
      rw [coeff_map,coeff_map,hg N le_rfl]
    · change coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom f)=
        coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom g)
      rw [coeff_map,coeff_map,hg N le_rfl]
lemma bounded_action_congr (D : ℕ) (u w : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (hf' : RegradeBound v Ω δ B w.val.val) (hi' : RegradeBound v Ω δ B w.inv.val)
    (he : ∀n≤B*D,coeff n u.val.val=coeff n w.val.val)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hg : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=
      coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded w hf' hi') g) := by
  intro d hd
  apply innerHom_coeff_congr
  · intro n hn
    exact rationalRegrade_congr_through v Ω hΩ δ k p hp B D he n (hn.trans hd)
  · intro n hn
    exact rationalRegrade_congr_through v Ω hΩ δ k p hp B D
      (oldUnit_inverse_congr v Ω δ k u w (B*D) he) n (hn.trans hd)
  · exact fun n hn=>hg n (hn.trans hd)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentBiTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.BiTruncation
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma hahn_negative (F : PowerSeries R) (z : ℤ) (hz : z<0) :
    (HahnSeries.ofPowerSeries ℤ R F).coeff z=0 := by
  rw [HahnSeries.ofPowerSeries_apply,HahnSeries.embDomain_of_notMem_range]
  rintro ⟨n,hn⟩
  simp only [Nat.castOrderEmbedding_apply] at hn
  omega
lemma hahn_nonnegative (x : HahnSeries ℤ R) (hx : ∀z<0,x.coeff z=0) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk (fun n=>x.coeff (n:ℤ)))=x := by
  apply HahnSeries.ext
  funext z
  rcases le_or_gt 0 z with hz|hz
  · lift z to ℕ using hz with n hn
    rw [HahnSeries.ofPowerSeries_apply_coeff,coeff_mk]
  · rw [hahn_negative _ _ hz,hx z hz]
lemma hahn_shift_commute (t : ℤ) (x : HahnSeries ℤ R) :
    HahnSeries.single t 1*x=x*HahnSeries.single t 1 := by
  apply HahnSeries.ext
  funext z
  simp only [HahnSeries.coeff_single_mul,HahnSeries.coeff_mul_single,one_mul,mul_one]
lemma hahn_shift_series_commute (t : ℤ) (f : PowerSeries (HahnSeries ℤ R)) :
    C (HahnSeries.single t 1)*f=f*C (HahnSeries.single t 1) := by
  apply PowerSeries.ext
  intro d
  rw [coeff_C_mul,coeff_mul_C,hahn_shift_commute]
lemma mul_coeff_congr {A : Type*} [Semiring A] (N : ℕ)
    {f f' g g' : PowerSeries A}
    (hf : ∀n≤N,coeff n f=coeff n f') (hg : ∀n≤N,coeff n g=coeff n g') :
    coeff N (f*g)=coeff N (f'*g') := by
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega),hg ij.2 (by omega)]
lemma finite_laurent_shift (f : PowerSeries (HahnSeries ℤ R)) (D : ℕ) :
    ∃c : ℤ,∃F : PowerSeries (PowerSeries R),∀d≤D,
      coeff d (C (HahnSeries.single (-c) 1)*f)=
        coeff d (PowerSeries.map (HahnSeries.ofPowerSeries ℤ R) F) := by
  classical
  have HB : BddBelow (Set.range (fun i : Fin (D+1)=>(coeff i.val f).order)) :=
    (Set.finite_range _).bddBelow
  obtain ⟨c,hc⟩:=HB
  let G:=C (HahnSeries.single (-c) 1)*f
  let F : PowerSeries (PowerSeries R):=PowerSeries.mk
    (fun d=>PowerSeries.mk (fun n=>(coeff d G).coeff (n:ℤ)))
  refine ⟨c,F,?_⟩
  intro d hd
  change coeff d G=_
  rw [coeff_map]
  dsimp only [F]
  rw [coeff_mk]
  symm
  apply hahn_nonnegative
  intro z hz
  change (coeff d (C (HahnSeries.single (-c) 1)*f)).coeff z=0
  rw [coeff_C_mul,HahnSeries.coeff_single_mul,one_mul]
  apply HahnSeries.coeff_eq_zero_of_lt_order
  have H:=hc (show (coeff d f).order∈Set.range (fun i : Fin (D+1)=>(coeff i.val f).order)
    from ⟨⟨d,by omega⟩,rfl⟩)
  omega

lemma inner_eventually (f : PowerSeries (HahnSeries ℤ R)) (D : ℕ) (z : ℤ) :
    ∃N : ℕ,∀U W : PowerSeries (PowerSeries R),Through N U 1 → Through N W 1 →
      (coeff D (PowerSeries.map (HahnSeries.ofPowerSeries ℤ R) U*f*
        PowerSeries.map (HahnSeries.ofPowerSeries ℤ R) W)).coeff z=(coeff D f).coeff z := by
  obtain ⟨c,F,hF⟩:=finite_laurent_shift f D
  refine ⟨D+(z-c).toNat,?_⟩
  intro U W hU hW
  let H:=HahnSeries.ofPowerSeries ℤ R
  let S : PowerSeries (HahnSeries ℤ R):=C (HahnSeries.single (-c) 1)
  have HE : coeff D (PowerSeries.map H U*(S*f)*PowerSeries.map H W)=
      coeff D (PowerSeries.map H (U*F*W)) := by
    rw [(PowerSeries.map H).map_mul (U*F) W,(PowerSeries.map H).map_mul U F]
    apply mul_coeff_congr D
    · intro n hn
      apply mul_coeff_congr n (fun _ _=>rfl)
      intro d hd
      exact hF d (hd.trans hn)
    · intro _ _;rfl
  have HS : PowerSeries.map H U*(S*f)*PowerSeries.map H W=
      S*(PowerSeries.map H U*f*PowerSeries.map H W) := by
    calc
      _=(PowerSeries.map H U*S)*f*PowerSeries.map H W := by simp only [mul_assoc]
      _=(S*PowerSeries.map H U)*f*PowerSeries.map H W := by
        rw [hahn_shift_series_commute]
      _=_ := by simp only [mul_assoc]
  rw [HS] at HE
  have HL:=congrArg (fun a : HahnSeries ℤ R=>a.coeff (z-c)) HE
  simp only [S,coeff_C_mul,HahnSeries.coeff_single_mul,one_mul,sub_neg_eq_add,
    sub_add_cancel,coeff_map] at HL
  rw [HL]
  have HF:=congrArg (fun a : HahnSeries ℤ R=>a.coeff (z-c)) (hF D le_rfl)
  simp only [coeff_C_mul,HahnSeries.coeff_single_mul,one_mul,sub_neg_eq_add,
    sub_add_cancel,coeff_map] at HF
  rw [HF]
  rcases le_or_gt 0 (z-c) with hz|hz
  · have hcast : ((z-c).toNat:ℤ)=z-c:=Int.toNat_of_nonneg hz
    rw [←hcast,HahnSeries.ofPowerSeries_apply_coeff,HahnSeries.ofPowerSeries_apply_coeff]
    exact Through.conjugate hU hW F D (z-c).toNat le_rfl
  · exact (hahn_negative _ _ hz).trans (hahn_negative _ _ hz).symm
end
end ElementaryPositivity.BiTruncation

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonRefinement
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
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_7
local instance instAddCommMonoidTorus_4_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_7_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_7_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma CrossingClose.action {D : ℕ} {c c' : ComparisonCrossing v Ω δ k B}
    (hc : CrossingClose v Ω δ k B D c c')
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hf : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B c f)=
      coeff d (comparisonAction v Ω hΩ δ k p hp B c' g) := by
  cases hc with
  | pure b=>
    intro d hd
    exact comparisonAction_input_congr v Ω hΩ δ k p hp B (.pure b) f g d
      (fun n hn=>hf n (hn.trans hd))
  | bounded u w hf hi hf' hi' he=>exact bounded_action_congr v Ω hΩ δ k p hp B D u w hf hi hf' hi' he f g ‹_›
lemma bounded_action_trivial (D : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (he : ∀n≤B*D,coeff n u.val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=coeff d f := by
  have H:=bounded_action_congr v Ω hΩ δ k p hp B D u 1 hf hi
    (RegradeBound.one v Ω δ B) (RegradeBound.one v Ω δ B) he f f (fun _ _=>rfl)
  intro d hd
  have HE:=H d hd
  change coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=
    coeff d (rationalRegrade v Ω hΩ k p hp δ B 1*f*rationalRegrade v Ω hΩ k p hp δ B 1) at HE
  simpa only [rationalRegrade_one,one_mul,mul_one] using HE
lemma WordRefines.action {D : ℕ} {l l' : List (ComparisonCrossing v Ω δ k B)}
    (hl : WordRefines v Ω δ k B D l l')
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hf : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonWordAction v Ω hΩ δ k p hp B l f)=
      coeff d (comparisonWordAction v Ω hΩ δ k p hp B l' g) := by
  induction hl with
  | nil=>exact hf
  | cons hc hl ih=>exact hc.action v Ω hΩ δ k p hp B _ _ ih
  | insert u hv hi he hl ih=>
    intro d hd
    rw [ih d hd]
    exact (bounded_action_trivial v Ω hΩ δ k p hp B D u hv hi he _ d hd).symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
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
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_9
local instance instAddCommMonoidTorus_6_r3afc47_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_6_r3afc47_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_9_r3afc47_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_9_r3afc47_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma finite_refinement_import_oai
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (D : ℕ) (l : List (ComparisonCrossing v Ω δ k B))
    (href : ∀N,∃l',WordRefines v Ω δ k B D l l' ∧ ∀n≤N,
      coeff n (comparisonWordOld v Ω hΩ δ k p hp hδ B l').val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    coeff D (comparisonWordAction v Ω hΩ δ k p hp B l f)=coeff D f := by
  apply expandFiber_injective v Ω hΩ k p hp
  apply HahnSeries.ext
  funext z
  obtain ⟨N,hN⟩:=BiTruncation.inner_eventually
    (PowerSeries.map (expandFiber v Ω hΩ k p) f) D z
  obtain ⟨l',hR,hloop⟩:=href N
  rw [hR.action v Ω hΩ δ k p hp B f f (fun _ _=>rfl) D le_rfl]
  have HW:=congrArg (fun a : PowerSeries (HahnSeries ℤ (Torus v Ω))=>(coeff D a).coeff z)
    (comparisonWord_expansion v Ω hΩ δ k p hp hδ B hq l' f)
  simp only [coeff_map] at HW
  rw [HW]
  let u:=comparisonWordOld v Ω hΩ δ k p hp hδ B l'
  have HU : BiTruncation.Through N (biRegrade v Ω δ k u.val.val) 1 := by
    simpa only [biRegrade_one] using biRegrade_through v Ω δ k N hloop
  have HI : BiTruncation.Through N (biRegrade v Ω δ k u.inv.val) 1 := by
    simpa [biRegrade_one] using biRegrade_through v Ω δ k N
      (oldUnit_inverse_congr v Ω δ k u 1 N hloop)
  have HE:=hN _ _ HU HI
  change (coeff D (oldLaurent v Ω δ k u.val.val*
    PowerSeries.map (expandFiber v Ω hΩ k p) f*oldLaurent v Ω δ k u.inv.val)).coeff z=_
  simpa only [oldLaurent,coeff_map] using HE

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElementaryPositivity.RationalFiber.finite_refinement_import_oai.{u_1, u_2} := @OAI.ElementaryPositivity.RationalFiber.finite_refinement_import_oai.{u_1, u_2}
