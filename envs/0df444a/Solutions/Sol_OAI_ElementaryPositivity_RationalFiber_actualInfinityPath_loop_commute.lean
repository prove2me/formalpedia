-- Prove2me | solution 1 for OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:16.046921+00:00
-- url     : https://prove2.me/submissions/0f898eb4-0ce9-4f80-99ef-ad19f6e8ba98

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom009
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_product_square
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualPath_rational_loop_coefficient

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
local instance rationalLaurentFaithfulRing_r8a11fc_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_r8a11fc_1 : NonUnitalSemiring (Torus v Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureComparisonIdentification
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
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalThroughRing
local instance rationalThroughAddCommMonoid_r8a11fc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup_r8a11fc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring_r8a11fc_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring_r8a11fc_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_4_r8a11fc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r8a11fc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_7_r8a11fc_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_7_r8a11fc_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (δ k : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_8
local instance instAddCommMonoidTorus_5_r8a11fc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_r8a11fc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_8_r8a11fc_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_8_r8a11fc_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma CrossingTrivial.mono {N K : ℕ} {c : ComparisonCrossing v Ω δ k B}
    (hc : CrossingTrivial v Ω δ k B N c) (h : K≤N) :
    CrossingTrivial v Ω δ k B K c := by
  cases hc with
  | bounded u hf hi he=>exact .bounded u hf hi (fun n hn=>he n (hn.trans h))

lemma CrossingClose.refl (D : ℕ) (c : ComparisonCrossing v Ω δ k B) :
    CrossingClose v Ω δ k B D c c := by
  cases c with
  | pure b=>exact .pure b
  | bounded u hf hi=>exact .bounded u u hf hi hf hi (fun _ _=>rfl)

lemma orientedBounded_trivial (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (b : Bool) (N : ℕ) (he : ∀n≤N,coeff n u.val.val=coeff n 1) :
    CrossingTrivial v Ω δ k B N (orientedBounded v Ω δ k B u hf hi b) := by
  cases b
  · exact .bounded u⁻¹ hi hf (oldUnit_inverse_congr v Ω δ k u 1 N he)
  · exact .bounded u hf hi he

lemma CrossingTrivial.insert {D : ℕ} {c : ComparisonCrossing v Ω δ k B}
    (hc : CrossingTrivial v Ω δ k B (B*D) c)
    {l l' : List (ComparisonCrossing v Ω δ k B)}
    (hl : WordRefines v Ω δ k B D l l') :
    WordRefines v Ω δ k B D l (c::l') := by
  cases hc with
  | bounded u hf hi he=>exact .insert u hf hi he hl

lemma filter_word_refines {A : Type*} (keep : A → Bool)
    (letter : A → ComparisonCrossing v Ω δ k B) (D : ℕ) (l : List A)
    (H : ∀a∈l,keep a=false → CrossingTrivial v Ω δ k B (B*D) (letter a)) :
    WordRefines v Ω δ k B D ((l.filter keep).map letter) (l.map letter) := by
  induction l with
  | nil=>exact .nil
  | cons a l ih=>
    have ih':=ih (fun a ha=>H a (List.mem_cons_of_mem _ ha))
    cases hh : keep a
    · simp only [List.filter_cons,hh,List.map_cons]
      exact (H a List.mem_cons_self hh).insert v Ω δ k B ih'
    · simp only [List.filter_cons,hh,↓reduceIte,List.map_cons]
      exact .cons (CrossingClose.refl v Ω δ k B D (letter a)) ih'
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonLine
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
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma actualLineLetter_high (a : ℝ) (N : ℕ) (hN : 1≤N)
    (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    CrossingTrivial LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) N
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) := by
  classical
  unfold actualLineLetter
  split
  · next hh=>
    split
    · next hp=>
      exact False.elim (ha (lineEvents_mono
        (realRootsThrough_mono C e hN) v k (line_cut_event C pc e L hdeg v k H a hp)))
    · apply orientedBounded_trivial
      exact line_chart_trivial C e L hdeg LaurentRay.vUnit Ω (simpleTotalTransport Ω C)
        N v k (H N) a ha
  · exact .bounded 1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _) (fun _ _=>rfl)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
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
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma actualLineWord_refines (lo hi : ℝ) (D A N : ℕ)
    (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    WordRefines LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) D
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi A)
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) := by
  classical
  unfold actualLineWord
  rw [←intervalEventList_filter C e v k lo hi hAN]
  apply filter_word_refines
  intro a ha hn
  have hnot : a∉intervalLineEvents C e v k lo hi A:=of_decide_eq_false hn
  exact (actualLineLetter_high Ω C coord hcoord pc e he S hS hcomp L hdeg v k H
    a A hA (event_not_retained C e v k lo hi a ha hnot)).mono _ _ _ _ _ hDA

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PathOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
lemma WordRefines.append {K M : Type*} [Field K] [AddCommGroup M]
    (u : Kˣ) (Ω : M →+ M →+ ℤ) (δ k : M →+ ℤ) (B D : ℕ)
    {l l' s s' : List (ComparisonCrossing u Ω δ k B)}
    (hl : WordRefines u Ω δ k B D l l') (hs : WordRefines u Ω δ k B D s s') :
    WordRefines u Ω δ k B D (l++s) (l'++s') := by
  induction hl with
  | nil=>exact hs
  | cons hc hl ih=>exact .cons hc ih
  | insert a hf hi he hl ih=>exact .insert a hf hi he ih

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

lemma actualPathWord_refines {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (D A N : ℕ) (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    WordRefines LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) D
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p A)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N) := by
  induction p with
  | nil=>exact .nil
  | append s p ih=>
    exact WordRefines.append _ _ _ _ _ _
      (actualLineWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg
        s.direction s.offset s.generic s.lo s.hi D A N hA hDA hAN) ih

end
end ElementaryPositivity.RationalFiber

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

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

lemma actualPathAction_coeff {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)))
    (D A : ℕ) (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) :
    coeff D (actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f)=
    coeff D (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p A) f) := by
  simp only [actualPathAction,PowerSeries.coeff_mk]
  exact (actualPathWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg p D
    (max 1 ((mutationSize Ω C pc+1)*D)) A (le_max_left _ _) (le_max_right _ _)
    (max_le hA hDA)).action _ _ _ _ _ _ _ _ f f (fun _ _=>rfl) D le_rfl

include he hdeg in
theorem actualPathAction_loop {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f=f := by
  apply PowerSeries.ext
  intro D
  simp only [actualPathAction,PowerSeries.coeff_mk]
  exact actualPath_rational_loop_coefficient Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p D f

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
local instance instNonUnitalSemiringTorus_11_r8a11fc_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_11_r8a11fc_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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

lemma coeff_commute_of_adjoints (u : (PowerSeries B)ˣ) (x : PowerSeries B) (D : ℕ)
    (h : ∀d≤D,coeff d (innerHom u x)=coeff d x) :
    coeff D (u.val*x)=coeff D (x*u.val) := by
  have H : coeff D (innerHom u x*u.val)=coeff D (x*u.val) := by
    apply ElementaryPositivity.FormalLog.mul_coeff_congr
    · exact h
    · exact fun _ _=>rfl
  change coeff D (((u.val*x)*u.inv)*u.val)=coeff D (x*u.val) at H
  simpa only [mul_assoc,u.inv_val,mul_one] using H
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
local instance infinityLaurentFiniteAddCommMonoid_r8a11fc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup_r8a11fc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring_r8a11fc_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring_r8a11fc_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_14
local instance instAddCommMonoidTorus_7_r8a11fc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_7_r8a11fc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma infinitySideHom_coeff_congr (pos : Bool)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (d : ℕ) (h : coeff d f=coeff d g) :
    coeff d (infinitySideHom v Ω hΩ k p pos f)=coeff d (infinitySideHom v Ω hΩ k p pos g) := by
  cases pos
  · change coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (PowerSeries.map (shearAction v _ _).toRingHom f))=
      coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (PowerSeries.map (shearAction v _ _).toRingHom g))
    simp only [coeff_map,h]
  · change coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f)=
      coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) g)
    simp only [coeff_map,h]

lemma infinity_embed_X (m : M) :
    expandFiberInfinity v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.X v Ω m))=
      HahnSeries.single (-k m) (Torus.X v Ω m) := by
  classical
  apply HahnSeries.ext
  funext z
  ext n
  rw [expandFiberInfinity_embed_coeff]
  by_cases hm : m=n
  · subst n
    simp only [HahnSeries.coeff_single,Torus.X,Torus.monomial,Finsupp.single_eq_same]
    split <;> simp_all
  · simp only [Torus.X,Torus.monomial,Finsupp.single_eq_of_ne (Ne.symm hm),ite_self,
      HahnSeries.coeff_single]
    split <;> simp_all

lemma infinitySideHom_test (pos : Bool) (m : M) :
    infinitySideHom v Ω hΩ k p pos (infinityTestInput v Ω hΩ k p hp pos m)=
      PowerSeries.C (HahnSeries.single (-k m) (Torus.X v Ω m)) := by
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    (mutationSideAction v _ _ pos ((mutationSideAction v _ _ pos).symm _))=_
  rw [RingEquiv.apply_symm_apply,PowerSeries.map_C,infinity_embed_X]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityFiniteLoop
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

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_7
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r8a11fc_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r8a11fc_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_r8a11fc_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_1
lemma actualInfinityPath_loop_commute_oai {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (m : M) :
    coeff d ((actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val*
      PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m)))=
    coeff d (PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m))*
      (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val) := by
  classical
  let pos:=decide (0<a (e (simpleRoot C pc)))
  let x:=infinityTestInput LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) pos m
  have hs:=actualInfinityPath_product_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N hN x
  have ht:=infinitySideHom_test LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) pos m
  apply coeff_commute_of_adjoints
  intro j hj
  rw [←ht]
  rw [hs]
  apply infinitySideHom_coeff_congr
  rw [←actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p x j N hN
    ((Nat.mul_le_mul_left _ hj).trans hdN)]
  rw [actualPathAction_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p x]

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute_oai.{u_1, u_2, u_3}
