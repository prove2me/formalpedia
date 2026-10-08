-- Prove2me | solution 1 for OAI.DeligneDrinfeld.ExactCountOrdering.transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:53:58.866235+00:00
-- url     : https://prove2.me/submissions/8ddc06a6-8c2b-410c-8a4e-08e844ef9668

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]

theorem below_mul {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈below wt n) (hq : q∈below wt m) : p*q∈below wt (n+m) :=
  mul_mem (by intros; simp_all; omega) hp hq

theorem deriv_homogeneous {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈homogeneous wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈homogeneous wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈homogeneous wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := homogeneous_mul (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (homogeneous wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp

theorem homogeneous_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈above wt n := space_mono (by intros; omega) hp
theorem homogeneous_below {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈below wt n := space_mono (by intros; omega) hp

theorem deriv_above {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈above wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := above_mul (hf a) (homogeneous_above (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := above_mul (homogeneous_above (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (above wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

theorem deriv_below {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈below wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈below wt n) : deriv f p∈below wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈below wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := below_mul (hf a) (homogeneous_below (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := below_mul (homogeneous_below (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (below wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

theorem deriv_sub (f g : α → A R α) (p : A R α) : deriv (fun a => f a-g a) p=deriv f p-deriv g p := by
  have hw (w : FreeMonoid α) : deriv (fun a => f a-g a) (word w)=deriv f (word w)-deriv g (word w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom,ih,mul_sub,sub_mul]
      abel
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simp only [map_add,hp,hq]; abel
  | smul c p hp => simp only [map_smul,hp,smul_sub]
end WordGrading

namespace TriangularWords
open AssociativeElimination WordGrading
variable {R α V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def apply (f : α → Module.End R V) (v : V) : A R α →ₗ[R] V :=
  (LinearMap.applyₗ v).comp (action f).toLinearMap
@[simp] theorem apply_word_one (f : α → Module.End R V) (v : V) : apply f v (word 1)=v := by simp [apply]
@[simp] theorem apply_word_cons (f : α → Module.End R V) (v : V) (a : α) (w : FreeMonoid α) :
    apply f v (word (FreeMonoid.of a*w))=f a (apply f v (word w)) := by
  simp [apply,Module.End.mul_apply]

theorem comparison (wt : α → ℕ) (H E : ℕ → Submodule R V)
    (f g : α → Module.End R V) (v : V) (hv : v∈H 0)
    (hg : ∀ a n z,z∈H n → g a z∈H (wt a+n))
    (hf : ∀ a n z,z∈E n → f a z∈E (wt a+n))
    (hfg : ∀ a n z,z∈H n → f a z-g a z∈E (wt a+n))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wt n) :
    apply g v p∈H n ∧ apply f v p-apply g v p∈E n := by
  have hw (w : FreeMonoid α) : apply g v (word w)∈H (degree wt w) ∧
      apply f v (word w)-apply g v (word w)∈E (degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simpa [apply] using And.intro hv ((E 0).zero_mem)
    | of_mul a w ih =>
      simp only [degree_mul,degree_of,apply_word_cons]
      refine ⟨hg a _ _ ih.1,?_⟩
      have h1 := hf a _ _ ih.2
      have h2 := hfg a _ _ ih.1
      have he : f a (apply f v (word w))-g a (apply g v (word w))=
          f a (apply f v (word w)-apply g v (word w))+
          (f a (apply g v (word w))-g a (apply g v (word w))) := by rw [map_sub]; abel
      rw [he]
      exact (E _).add_mem h1 h2
  constructor
  · exact map_space (apply g v) _ (by intro w hw'; simpa only [hw'] using (hw w).1) hp
  · exact map_space (apply f v-apply g v) _ (by intro w hw'; simpa only [hw',LinearMap.sub_apply] using (hw w).2) hp
end TriangularWords
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem homogeneous_mul_strictlyBelow {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈strictlyBelow wt m) : p*q∈strictlyBelow wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq
theorem strictlyBelow_mul_homogeneous {wt : α → ℕ} {n m : ℕ} {p q : A R α}
    (hp : p∈strictlyBelow wt n) (hq : q∈homogeneous wt m) : p*q∈strictlyBelow wt (n+m) :=
  mul_mem (by intros; simp_all) hp hq

theorem deriv_strictlyBelow {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈strictlyBelow wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈strictlyBelow wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈strictlyBelow wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := strictlyBelow_mul_homogeneous (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul_strictlyBelow (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (strictlyBelow wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp
end WordGrading
namespace TensorGrading
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
def space (P : FreeMonoid α → FreeMonoid β → Prop) : Submodule R (V (R:=R) (α:=α) (β:=β)) :=
  Submodule.span R {z | ∃ u v,P u v ∧ z=word u⊗ₜ word v}
theorem tmul_word_mem {P : FreeMonoid α → FreeMonoid β → Prop} (u : FreeMonoid α) (v : FreeMonoid β)
    (h : P u v) : word (R:=R) u⊗ₜ word (R:=R) v∈space P :=
  Submodule.subset_span ⟨u,v,h,rfl⟩
theorem space_mono {P Q : FreeMonoid α → FreeMonoid β → Prop} (h : ∀ u v,P u v → Q u v) :
    space (R:=R) P ≤ space Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u,v,huv,rfl⟩
  exact tmul_word_mem u v (h u v huv)
theorem tmul_mem {P : FreeMonoid α → Prop} {Q : FreeMonoid β → Prop}
    {T : FreeMonoid α → FreeMonoid β → Prop} (h : ∀ u v,P u → Q v → T u v)
    {p : A R α} {q : A R β} (hp : p∈WordGrading.space P) (hq : q∈WordGrading.space Q) :
    p⊗ₜ q∈space T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq => obtain ⟨v,hv,rfl⟩ := hq; exact tmul_word_mem _ _ (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [TensorProduct.tmul_add] using (space T).add_mem hp hq
    | smul c p _ hp => simpa only [TensorProduct.tmul_smul] using (space T).smul_mem c hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [TensorProduct.add_tmul] using (space T).add_mem hp hq
  | smul c p _ hp => simpa only [TensorProduct.smul_tmul'] using (space T).smul_mem c hp

def homogeneous (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v=n)
def above (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => n≤degree wa u+degree wb v)
def below (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v≤n)
def strictlyBelow (wa : α → ℕ) (wb : β → ℕ) (n : ℕ) :=
  space (R:=R) (fun u v => degree wa u+degree wb v<n)

theorem map_space {M : Type*} [AddCommGroup M] [Module R M] (f : V (R:=R) (α:=α) (β:=β) →ₗ[R] M)
    {P : FreeMonoid α → FreeMonoid β → Prop} (Q : Submodule R M)
    (hf : ∀ u v,P u v → f (word u⊗ₜ word v)∈Q) {p : V (R:=R) (α:=α) (β:=β)} (hp : p∈space P) : f p∈Q := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,v,h,rfl⟩ := hp; exact hf u v h
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Q.add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using Q.smul_mem c hp

theorem homo_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.homogeneous wa n) (hq : q∈WordGrading.homogeneous wb m) :
    p⊗ₜ q∈homogeneous wa wb (n+m) := tmul_mem (by intros; simp_all) hp hq
theorem above_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.above wa n) (hq : q∈WordGrading.above wb m) :
    p⊗ₜ q∈above wa wb (n+m) := tmul_mem (by intros; omega) hp hq
theorem below_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.below wa n) (hq : q∈WordGrading.below wb m) :
    p⊗ₜ q∈below wa wb (n+m) := tmul_mem (by intros; omega) hp hq
theorem strict_homo_tmul {wa : α → ℕ} {wb : β → ℕ} {n m : ℕ} {p : A R α} {q : A R β}
    (hp : p∈WordGrading.strictlyBelow wa n) (hq : q∈WordGrading.homogeneous wb m) :
    p⊗ₜ q∈strictlyBelow wa wb (n+m) := tmul_mem (by intros; omega) hp hq

variable {wa : α → ℕ} {wb : β → ℕ} {δ : β → α → A R α}
theorem op_homogeneous (hδ : ∀ b a,δ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z∈homogeneous wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.homogeneous wa (degree wa u) := word_mem u rfl
  have hv : word (R:=R) v∈WordGrading.homogeneous wb (degree wb v) := word_mem v rfl
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.homogeneous wa (wa a) := word_mem (FreeMonoid.of a) (degree_of wa a)
    have h := homo_tmul (WordGrading.homogeneous_mul ha hu) hv
    simpa only [PolynomialOrdering.op,Sum.elim_inl,PolynomialOrdering.fiberOp_tmul,← huv,Nat.add_assoc] using h
  | inr b =>
    have hd := WordGrading.deriv_homogeneous (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.homogeneous wb (wb b) := word_mem (FreeMonoid.of b) (degree_of wb b)
    have h1 := homo_tmul hd hv
    have h2 := homo_tmul hu (WordGrading.homogeneous_mul hb hv)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈homogeneous wa wb (wb b+n)
    apply (homogeneous wa wb (wb b+n)).add_mem
    · simpa only [← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · simpa only [← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem op_above (hδ : ∀ b a,δ b a∈WordGrading.above wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈above wa wb n) :
    PolynomialOrdering.op δ s z∈above wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.above wa (degree wa u) := word_mem u (by rfl)
  have hv : word (R:=R) v∈WordGrading.above wb (degree wb v) := word_mem v (by rfl)
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.above wa (wa a) := word_mem (FreeMonoid.of a) (by simp)
    have h := above_tmul (WordGrading.above_mul ha hu) hv
    have hm : above (R:=R) wa wb (wa a+degree wa u+degree wb v) ≤ above wa wb (wa a+n) :=
      space_mono (by intro u' v' hh; change n ≤ degree wa u+degree wb v at huv; omega)
    exact hm h
  | inr b =>
    have hd := WordGrading.deriv_above (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.above wb (wb b) := word_mem (FreeMonoid.of b) (by simp)
    have h1 := above_tmul hd hv
    have h2 := above_tmul hu (WordGrading.above_mul hb hv)
    have hm : above (R:=R) wa wb (degree wa u+degree wb v+wb b) ≤ above wa wb (wb b+n) :=
      space_mono (by intro u' v' hh; change n ≤ degree wa u+degree wb v at huv; omega)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈above wa wb (wb b+n)
    apply ( above wa wb (wb b+n)).add_mem
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem op_below (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈below wa wb n) :
    PolynomialOrdering.op δ s z∈below wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hu : word (R:=R) u∈WordGrading.below wa (degree wa u) := word_mem u (by rfl)
  have hv : word (R:=R) v∈WordGrading.below wb (degree wb v) := word_mem v (by rfl)
  cases s with
  | inl a =>
    have ha : atom (R:=R) a∈WordGrading.below wa (wa a) := word_mem (FreeMonoid.of a) (by simp)
    have h := below_tmul (WordGrading.below_mul ha hu) hv
    have hm : below (R:=R) wa wb (wa a+degree wa u+degree wb v) ≤ below wa wb (wa a+n) :=
      space_mono (by intro u' v' hh; change degree wa u+degree wb v ≤ n at huv; omega)
    exact hm h
  | inr b =>
    have hd := WordGrading.deriv_below (c:=wb b) (f:=δ b) (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hb : atom (R:=R) b∈WordGrading.below wb (wb b) := word_mem (FreeMonoid.of b) (by simp)
    have h1 := below_tmul hd hv
    have h2 := below_tmul hu (WordGrading.below_mul hb hv)
    have hm : below (R:=R) wa wb (degree wa u+degree wb v+wb b) ≤ below wa wb (wb b+n) :=
      space_mono (by intro u' v' hh; change degree wa u+degree wb v ≤ n at huv; omega)
    change deriv (δ b) (word u)⊗ₜ word v+word u⊗ₜ (atom b*word v)∈below wa wb (wb b+n)
    apply ( below wa wb (wb b+n)).add_mem
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
    · apply hm; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem op_strictlyBelow (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈strictlyBelow wa wb n) :
    PolynomialOrdering.op δ s z∈strictlyBelow wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s) _ ?_ hz
  intro u v huv
  have hh : word (R:=R) u⊗ₜ word (R:=R) v∈below wa wb (degree wa u+degree wb v) := tmul_word_mem u v (by rfl)
  have h := op_below hδ s hh
  have hm : below (R:=R) wa wb (Sum.elim wa wb s+(degree wa u+degree wb v)) ≤
      strictlyBelow wa wb (Sum.elim wa wb s+n) :=
    space_mono (by intro u' v' hh; change degree wa u+degree wb v<n at huv; omega)
  exact hm h

variable {δ₀ : β → α → A R α}
theorem op_difference (s : Sum α β) (u : FreeMonoid α) (v : FreeMonoid β) :
    (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) (word u⊗ₜ word v)=
    Sum.elim (fun _ => 0) (fun b => deriv (fun a => δ b a-δ₀ b a) (word u)⊗ₜ word v) s := by
  cases s with
  | inl a => simp [PolynomialOrdering.op]
  | inr b =>
    simp only [PolynomialOrdering.op,Sum.elim_inr,LinearMap.sub_apply,PolynomialOrdering.baseOp_tmul,
      WordGrading.deriv_sub,TensorProduct.sub_tmul]
    abel

theorem op_difference_above (hδ : ∀ b a,δ b a-δ₀ b a∈WordGrading.above wa (wb b+wa a+1))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z-PolynomialOrdering.op δ₀ s z∈above wa wb (Sum.elim wa wb s+n+1) := by
  apply map_space (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) _ ?_ hz
  intro u v huv
  rw [op_difference]
  cases s with
  | inl a => exact (above wa wb _).zero_mem
  | inr b =>
    have hu : word (R:=R) u∈WordGrading.above wa (degree wa u) := word_mem u (by rfl)
    have hv : word (R:=R) v∈WordGrading.above wb (degree wb v) := word_mem v (by rfl)
    have hd := WordGrading.deriv_above (c:=wb b+1) (f:=fun a => δ b a-δ₀ b a)
      (by intro a; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hδ b a) hu
    have hh := above_tmul hd hv
    simpa only [Sum.elim_inr,← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem op_difference_below (hδ : ∀ b a,δ b a-δ₀ b a∈WordGrading.strictlyBelow wa (wb b+wa a))
    (s : Sum α β) {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈homogeneous wa wb n) :
    PolynomialOrdering.op δ s z-PolynomialOrdering.op δ₀ s z∈strictlyBelow wa wb (Sum.elim wa wb s+n) := by
  apply map_space (PolynomialOrdering.op δ s-PolynomialOrdering.op δ₀ s) _ ?_ hz
  intro u v huv
  rw [op_difference]
  cases s with
  | inl a => exact (strictlyBelow wa wb _).zero_mem
  | inr b =>
    have hu : word (R:=R) u∈WordGrading.homogeneous wa (degree wa u) := word_mem u rfl
    have hv : word (R:=R) v∈WordGrading.homogeneous wb (degree wb v) := word_mem v rfl
    have hd := WordGrading.deriv_strictlyBelow (c:=wb b) (f:=fun a => δ b a-δ₀ b a)
      (by intro a; simpa only [Nat.add_comm] using hδ b a) hu
    have hh := strict_homo_tmul hd hv
    simpa only [Sum.elim_inr,← huv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem comparison_above (h0 : ∀ b a,δ₀ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈WordGrading.above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈WordGrading.above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈WordGrading.homogeneous (Sum.elim wa wb) n) :
    PolynomialOrdering.normalize δ₀ p∈homogeneous wa wb n ∧
    PolynomialOrdering.normalize δ p-PolynomialOrdering.normalize δ₀ p∈above wa wb (n+1) := by
  apply TriangularWords.comparison (Sum.elim wa wb) (homogeneous wa wb) (fun n => above wa wb (n+1))
    (PolynomialOrdering.op δ) (PolynomialOrdering.op δ₀) (1⊗ₜ 1) ?_ ?_ ?_ ?_ hp
  · exact tmul_word_mem 1 1 (by simp)
  · intro a n z hz; exact op_homogeneous h0 a hz
  · intro a n z hz; simpa only [Nat.add_assoc] using op_above hδ a hz
  · intro a n z hz; exact op_difference_above hd a hz

theorem comparison_below (h0 : ∀ b a,δ₀ b a∈WordGrading.homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈WordGrading.below wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈WordGrading.strictlyBelow wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈WordGrading.homogeneous (Sum.elim wa wb) n) :
    PolynomialOrdering.normalize δ₀ p∈homogeneous wa wb n ∧
    PolynomialOrdering.normalize δ p-PolynomialOrdering.normalize δ₀ p∈strictlyBelow wa wb n := by
  apply TriangularWords.comparison (Sum.elim wa wb) (homogeneous wa wb) (strictlyBelow wa wb)
    (PolynomialOrdering.op δ) (PolynomialOrdering.op δ₀) (1⊗ₜ 1) ?_ ?_ ?_ ?_ hp
  · exact tmul_word_mem 1 1 (by simp)
  · intro a n z hz; exact op_homogeneous h0 a hz
  · intro a n z hz; exact op_strictlyBelow hδ a hz
  · intro a n z hz; exact op_difference_below hd a hz
end TensorGrading
namespace CountTables

section
open AssociativeElimination

open WordGrading

theorem bracket_homo {n m : ℕ} {p q : A K F}
    (hp : p∈homogeneous fiberCount n) (hq : q∈homogeneous fiberCount m) :
    bracket p q∈homogeneous fiberCount (n+m) := by
  apply (homogeneous fiberCount (n+m)).sub_mem (homogeneous_mul hp hq)
  simpa only [Nat.add_comm] using homogeneous_mul hq hp

theorem H_homo : H∈homogeneous fiberCount 0 := word_mem (FreeMonoid.of 0) rfl
theorem U_homo (i : Fin 2) : U i∈homogeneous fiberCount 1 := by
  apply word_mem
  fin_cases i <;> rfl
theorem V_homo (i : Fin 2) : V i∈homogeneous fiberCount 0 := by
  apply word_mem
  fin_cases i <;> rfl
theorem R_homo (i : Fin 2) : R' i∈homogeneous fiberCount 1 := by
  have h := bracket_homo H_homo (U_homo i)
  exact h
theorem Q_homo (i : Fin 2) : Q i∈homogeneous fiberCount 1 :=
  by
    have h := bracket_homo ((homogeneous fiberCount 0).add_mem H_homo (V_homo i)) (U_homo i)
    exact h
theorem W_homo : W∈homogeneous fiberCount 1 :=
  by
    have h1 := bracket_homo (V_homo 0) (U_homo 1)
    have h2 := bracket_homo (U_homo 0) (V_homo 1)
    exact (homogeneous fiberCount 1).add_mem h1 h2

theorem common_homo_0 (a : F) : common 0 a∈homogeneous fiberCount (baseCount 0+fiberCount a) := by
  fin_cases a
  · have h := bracket_homo H_homo (V_homo 0)
    exact h
  · have h := Q_homo 0
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo H_homo (V_homo 0)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
theorem common_homo_1 (a : F) : common 1 a∈homogeneous fiberCount (baseCount 1+fiberCount a) := by
  fin_cases a
  · have h := bracket_homo H_homo (V_homo 1)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := Q_homo 1
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo H_homo (V_homo 1)
    exact h
theorem common_homo_2 (a : F) : common 2 a∈homogeneous fiberCount (baseCount 2+fiberCount a) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (U_homo 0) (U_homo 1)
    exact h
  · have h := bracket_homo (U_homo 0) (U_homo 1)
    exact h
  · have h := W_homo
    exact h
  · have h := W_homo
    exact h
theorem common_homo_3 (a : F) : common 3 a∈homogeneous fiberCount (baseCount 3+fiberCount a) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (U_homo 0) (V_homo 1)
    exact h
  · have h := bracket_homo (U_homo 1) (V_homo 0)
    exact h
  · have h := bracket_homo (V_homo 0) (V_homo 1)
    exact h
  · have h := bracket_homo (V_homo 0) (V_homo 1)
    exact h
theorem common_homo (b : B) (a : F) : common b a∈homogeneous fiberCount (baseCount b+fiberCount a) := by
  fin_cases b
  · exact common_homo_0 a
  · exact common_homo_1 a
  · exact common_homo_2 a
  · exact common_homo_3 a
theorem higher_homo_0 (a : F) : higher 0 a∈homogeneous fiberCount (baseCount 0+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo (R_homo 0) (U_homo 0)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (bracket_homo (V_homo 0) (U_homo 0)) (U_homo 0)
    exact h
  · have h := bracket_homo (Q_homo 0) (U_homo 1)
    exact h
theorem higher_homo_1 (a : F) : higher 1 a∈homogeneous fiberCount (baseCount 1+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo (R_homo 1) (U_homo 1)
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h := bracket_homo (Q_homo 1) (U_homo 0)
    exact h
  · have h := bracket_homo (bracket_homo (V_homo 1) (U_homo 1)) (U_homo 1)
    exact h
theorem higher_homo_2 (a : F) : higher 2 a∈homogeneous fiberCount (baseCount 2+fiberCount a+2) := by
  fin_cases a
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
theorem higher_homo_3 (a : F) : higher 3 a∈homogeneous fiberCount (baseCount 3+fiberCount a+2) := by
  fin_cases a
  · have h := bracket_homo H_homo (bracket_homo (U_homo 0) (U_homo 1))
    exact h
  · exact (homogeneous fiberCount _).zero_mem
  · exact (homogeneous fiberCount _).zero_mem
  · have h1 := bracket_homo W_homo (U_homo 0)
    have h2 := bracket_homo (U_homo 0) (R_homo 1)
    exact (homogeneous fiberCount 2).add_mem h1 h2
  · have h1 := bracket_homo W_homo (U_homo 1)
    have h2 := bracket_homo (U_homo 1) (R_homo 0)
    exact (homogeneous fiberCount 2).add_mem h1 h2
theorem higher_homo (b : B) (a : F) : higher b a∈homogeneous fiberCount (baseCount b+fiberCount a+2) := by
  fin_cases b
  · exact higher_homo_0 a
  · exact higher_homo_1 a
  · exact higher_homo_2 a
  · exact higher_homo_3 a

theorem lower_strict (b : B) (a : F) : lower b a∈strictlyBelow fiberCount (baseCount b+fiberCount a) := by
  fin_cases b <;> fin_cases a <;> simp only [lower,baseCount,fiberCount,Nat.reduceAdd]
  all_goals first
    | exact (strictlyBelow fiberCount _).zero_mem
    | exact (space_mono (P:=fun w => degree fiberCount w=0) (Q:=fun w => degree fiberCount w<1)
        (by intros; omega)) (bracket_homo (n:=0) (m:=0) (V_homo 0) (V_homo 1))

theorem source_above (b : B) (a : F) : source b a∈above fiberCount (baseCount b+fiberCount a) := by
  apply (above fiberCount _).add_mem
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a) (by intros; omega)
    exact common_homo b a
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a+2) (by intros; omega)
    exact higher_homo b a

theorem source_difference (b : B) (a : F) :
    source b a-common b a∈above fiberCount (baseCount b+fiberCount a+1) := by
  rw [source,add_sub_cancel_left]
  apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a+2) (by intros; omega)
  exact higher_homo b a

theorem target_below (b : B) (a : F) : target b a∈below fiberCount (baseCount b+fiberCount a) := by
  apply (below fiberCount _).add_mem
  · apply space_mono (P:=fun w => degree fiberCount w=baseCount b+fiberCount a) (by intros; omega)
    exact common_homo b a
  · apply space_mono (P:=fun w => degree fiberCount w<baseCount b+fiberCount a) (by intros; omega)
    exact lower_strict b a

theorem target_difference (b : B) (a : F) :
    target b a-common b a∈strictlyBelow fiberCount (baseCount b+fiberCount a) := by
  rw [target,add_sub_cancel_left]
  exact lower_strict b a

end

open AssociativeElimination

attribute [local irreducible] X Y C H U V
end CountTables

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]
variable (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)

theorem algHom_homogeneous (hf : ∀ a,f (atom a)∈homogeneous wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) : f p∈homogeneous wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈homogeneous wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (degree_one wb)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact homogeneous_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w h
  change f (word w)∈homogeneous wb n
  rw [← h]
  exact hw w

theorem algHom_above (hf : ∀ a,f (atom a)∈above wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈above wa n) : f p∈above wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈above wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (by simp)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact above_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change n≤degree wa w at hn; change degree wa w≤degree wb v at hv; omega) (hw w)

theorem algHom_below (hf : ∀ a,f (atom a)∈below wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈below wa n) : f p∈below wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈below wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (by simp)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact below_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change degree wa w≤n at hn; change degree wb v≤degree wa w at hv; omega) (hw w)

end WordGrading
namespace PolynomialOrdering
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β γ : Type*} [CommRing R]

variable (wa : α → ℕ) (wb : β → ℕ)
theorem fiberIn_homogeneous {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    fiberIn (β:=β) p∈homogeneous (Sum.elim wa wb) n := by
  apply algHom_homogeneous _ wa _ ?_ hp
  intro a
  change fiberIn (atom a)∈homogeneous (Sum.elim wa wb) (wa a)
  rw [fiberIn,lift_atom]
  exact word_mem (FreeMonoid.of (.inl a : Sum α β)) (degree_of (Sum.elim wa wb) (.inl a))

theorem baseIn_homogeneous {n : ℕ} {p : A R β} (hp : p∈homogeneous wb n) :
    baseIn (α:=α) p∈homogeneous (Sum.elim wa wb) n := by
  apply algHom_homogeneous _ wb _ ?_ hp
  intro a
  change baseIn (atom a)∈homogeneous (Sum.elim wa wb) (wb a)
  rw [baseIn,lift_atom]
  exact word_mem (FreeMonoid.of (.inr a : Sum α β)) (degree_of (Sum.elim wa wb) (.inr a))

theorem merge_word_homogeneous (u : FreeMonoid α) (v : FreeMonoid β) :
    merge (word (R:=R) u⊗ₜ word (R:=R) v)∈homogeneous (Sum.elim wa wb) (degree wa u+degree wb v) := by
  exact homogeneous_mul (fiberIn_homogeneous wa wb (word_mem u rfl))
    (baseIn_homogeneous wa wb (word_mem v rfl))

theorem merge_homogeneous {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)}
    (hz : z∈TensorGrading.homogeneous wa wb n) : merge z∈homogeneous (Sum.elim wa wb) n := by
  apply TensorGrading.map_space merge _ ?_ hz
  intro u v h
  simpa only [h] using merge_word_homogeneous (R:=R) wa wb u v

theorem merge_above {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)}
    (hz : z∈TensorGrading.above wa wb n) : merge z∈above (Sum.elim wa wb) n := by
  apply TensorGrading.map_space merge _ ?_ hz
  intro u v h
  exact space_mono (by intro w hw; change n≤degree wa u+degree wb v at h; change degree (Sum.elim wa wb) w=degree wa u+degree wb v at hw; omega)
    (merge_word_homogeneous (R:=R) wa wb u v)

variable {δ δ₀ : β → α → A R α}
theorem ordered_comparison_above (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    ordered δ₀ p∈homogeneous (Sum.elim wa wb) n ∧
    ordered δ p-ordered δ₀ p∈above (Sum.elim wa wb) (n+1) := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_above h0 hδ hd hp
  exact ⟨merge_homogeneous wa wb h1,by simpa only [ordered,LinearMap.comp_apply,map_sub] using merge_above wa wb h2⟩

theorem normalize_homogeneous (hδ : ∀ b a,δ b a∈homogeneous wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    normalize δ p∈TensorGrading.homogeneous wa wb n := by
  have hw (w : FreeMonoid (Sum α β)) : normalize δ (word w)∈
      TensorGrading.homogeneous wa wb (degree (Sum.elim wa wb) w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,normalize_one,degree_one]
      exact TensorGrading.tmul_word_mem 1 1 (by simp)
    | of_mul a w ih =>
      rw [word_mul,word_of,normalize_atom_mul,degree_mul,degree_of]
      exact TensorGrading.op_homogeneous hδ a ih
  apply WordGrading.map_space (normalize δ) _ ?_ hp
  intro w hn
  rw [← hn]
  exact hw w

theorem normalize_above (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈above (Sum.elim wa wb) n) :
    normalize δ p∈TensorGrading.above wa wb n := by
  have hw (w : FreeMonoid (Sum α β)) : normalize δ (word w)∈
      TensorGrading.above wa wb (degree (Sum.elim wa wb) w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,normalize_one,degree_one]
      exact TensorGrading.tmul_word_mem 1 1 (by simp)
    | of_mul a w ih =>
      rw [word_mul,word_of,normalize_atom_mul,degree_mul,degree_of]
      exact TensorGrading.op_above hδ a ih
  apply WordGrading.map_space (normalize δ) _ ?_ hp
  intro w hn
  exact TensorGrading.space_mono (by intro u v huv; change n≤degree (Sum.elim wa wb) w at hn; change degree (Sum.elim wa wb) w≤degree wa u+degree wb v at huv; omega) (hw w)

theorem baseStage_homogeneous (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈homogeneous wb n → f p∈homogeneous wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.homogeneous wa wb n) :
    baseStage f z∈homogeneous (Sum.elim wa wb) n := by
  apply TensorGrading.map_space (baseStage f) _ ?_ hz
  intro u v hn
  rw [baseStage_tmul,← hn]
  exact homogeneous_mul (fiberIn_homogeneous wa wb (word_mem u rfl))
    (baseIn_homogeneous wa wb (hf _ _ (word_mem v rfl)))

theorem baseIn_above {n : ℕ} {p : A R β} (hp : p∈above wb n) :
    baseIn (α:=α) p∈above (Sum.elim wa wb) n := by
  apply algHom_above _ wb _ ?_ hp
  intro a
  exact homogeneous_above (baseIn_homogeneous wa wb (word_mem (FreeMonoid.of a) (degree_of wb a)))

theorem baseIn_strictlyBelow {n : ℕ} {p : A R β} (hp : p∈strictlyBelow wb n) :
    baseIn (α:=α) p∈strictlyBelow (Sum.elim wa wb) n := by
  apply WordGrading.map_space baseIn.toLinearMap _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; change degree wb w<n at hn; change degree (Sum.elim wa wb) v=degree wb w at hv; omega)
    (baseIn_homogeneous (R:=R) wa wb (word_mem w rfl))

theorem baseStage_above (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈above wb n → f p∈above wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.above wa wb n) :
    baseStage f z∈above (Sum.elim wa wb) n := by
  apply TensorGrading.map_space (baseStage f) _ ?_ hz
  intro u v hn
  have h := above_mul (homogeneous_above (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl)))
    (baseIn_above wa wb (hf _ _ (word_mem v (le_refl _))))
  exact space_mono (by intro w hw; change n≤degree wa u+degree wb v at hn; change degree wa u+degree wb v≤degree (Sum.elim wa wb) w at hw; omega) h

theorem baseStage_strictlyBelow (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈below wb n → f p∈below wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.strictlyBelow wa wb n) :
    baseStage f z∈strictlyBelow (Sum.elim wa wb) n := by
  apply TensorGrading.map_space (baseStage f) _ ?_ hz
  intro u v hn
  have hb : baseIn (α:=α) (f (word v))∈below (Sum.elim wa wb) (degree wb v) := by
    apply algHom_below _ wb _ ?_ (hf _ _ (word_mem v (le_refl _)))
    intro a
    exact homogeneous_below (baseIn_homogeneous wa wb (word_mem (FreeMonoid.of a) (degree_of wb a)))
  have h := below_mul (homogeneous_below (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl))) hb
  exact space_mono (by intro w hw; change degree wa u+degree wb v<n at hn; change degree (Sum.elim wa wb) w≤degree wa u+degree wb v at hw; omega) h

theorem baseStage_difference_above (f g : A R β →ₗ[R] A R β)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈above wb (n+1))
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.homogeneous wa wb n) :
    baseStage f z-baseStage g z∈above (Sum.elim wa wb) (n+1) := by
  rw [← LinearMap.sub_apply]
  apply TensorGrading.map_space (baseStage f-baseStage g) _ ?_ hz
  intro u v hn
  change fiberIn (word u)*baseIn (f (word v))-fiberIn (word u)*baseIn (g (word v))∈_
  rw [← mul_sub,← map_sub]
  have h := above_mul (homogeneous_above (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl)))
    (baseIn_above wa wb (hfg _ _ (word_mem v rfl)))
  simpa only [← Nat.add_assoc,hn] using h

theorem baseStage_difference_below (f g : A R β →ₗ[R] A R β)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈strictlyBelow wb n)
    {n : ℕ} {z : V (R:=R) (α:=α) (β:=β)} (hz : z∈TensorGrading.homogeneous wa wb n) :
    baseStage f z-baseStage g z∈strictlyBelow (Sum.elim wa wb) n := by
  rw [← LinearMap.sub_apply]
  apply TensorGrading.map_space (baseStage f-baseStage g) _ ?_ hz
  intro u v hn
  change fiberIn (word u)*baseIn (f (word v))-fiberIn (word u)*baseIn (g (word v))∈_
  rw [← mul_sub,← map_sub]
  have h := homogeneous_mul_strictlyBelow (fiberIn_homogeneous wa wb (word_mem (R:=R) u rfl))
    (baseIn_strictlyBelow wa wb (hfg _ _ (word_mem v rfl)))
  simpa only [hn] using h

theorem iterated_comparison_above (f g : A R β →ₗ[R] A R β)
    (hg : ∀ n p,p∈homogeneous wb n → g p∈homogeneous wb n)
    (hf : ∀ n p,p∈above wb n → f p∈above wb n)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈above wb (n+1))
    (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈above wa (wb b+wa a+1))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    iterated δ₀ g p∈homogeneous (Sum.elim wa wb) n ∧
    iterated δ f p-iterated δ₀ g p∈above (Sum.elim wa wb) (n+1) := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_above h0 hδ hd hp
  refine ⟨baseStage_homogeneous wa wb g hg h1,?_⟩
  have hf1 := baseStage_above wa wb f hf h2
  have hfg1 := baseStage_difference_above wa wb f g hfg h1
  have he : iterated δ f p-iterated δ₀ g p=
      baseStage f (normalize δ p-normalize δ₀ p)+
      (baseStage f (normalize δ₀ p)-baseStage g (normalize δ₀ p)) := by
    simp only [iterated,LinearMap.comp_apply,map_sub]
    abel
  rw [he]
  exact (above (Sum.elim wa wb) (n+1)).add_mem hf1 hfg1

theorem iterated_comparison_below (f g : A R β →ₗ[R] A R β)
    (hg : ∀ n p,p∈homogeneous wb n → g p∈homogeneous wb n)
    (hf : ∀ n p,p∈below wb n → f p∈below wb n)
    (hfg : ∀ n p,p∈homogeneous wb n → f p-g p∈strictlyBelow wb n)
    (h0 : ∀ b a,δ₀ b a∈homogeneous wa (wb b+wa a))
    (hδ : ∀ b a,δ b a∈below wa (wb b+wa a))
    (hd : ∀ b a,δ b a-δ₀ b a∈strictlyBelow wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈homogeneous (Sum.elim wa wb) n) :
    iterated δ₀ g p∈homogeneous (Sum.elim wa wb) n ∧
    iterated δ f p-iterated δ₀ g p∈strictlyBelow (Sum.elim wa wb) n := by
  obtain ⟨h1,h2⟩ := TensorGrading.comparison_below h0 hδ hd hp
  refine ⟨baseStage_homogeneous wa wb g hg h1,?_⟩
  have hf1 := baseStage_strictlyBelow wa wb f hf h2
  have hfg1 := baseStage_difference_below wa wb f g hfg h1
  have he : iterated δ f p-iterated δ₀ g p=
      baseStage f (normalize δ p-normalize δ₀ p)+
      (baseStage f (normalize δ₀ p)-baseStage g (normalize δ₀ p)) := by
    simp only [iterated,LinearMap.comp_apply,map_sub]
    abel
  rw [he]
  exact (strictlyBelow (Sum.elim wa wb) n).add_mem hf1 hfg1

theorem iterated_above (f : A R β →ₗ[R] A R β)
    (hf : ∀ n p,p∈above wb n → f p∈above wb n)
    (hδ : ∀ b a,δ b a∈above wa (wb b+wa a))
    {n : ℕ} {p : A R (Sum α β)} (hp : p∈above (Sum.elim wa wb) n) :
    iterated δ f p∈above (Sum.elim wa wb) n :=
  baseStage_above wa wb f hf (normalize_above wa wb hδ hp)

end PolynomialOrdering
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem eq_zero_of_homogeneous_above (wt : α → ℕ) (n : ℕ) {p : A R α}
    (hp : p∈homogeneous wt n) (hq : p∈above wt (n+1)) : p=0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_cases hw : degree wt w=n
  · exact coeff_support hq w (by omega)
  · exact coeff_support hp w hw

theorem count_transfer (wt : α → ℕ) (S C T : A R α →ₗ[R] A R α)
    (n : ℕ) (p e : A R α)
    (hC : C p∈homogeneous wt n)
    (hSC : S p-C p∈above wt (n+1))
    (hTC : T p-C p∈strictlyBelow wt n)
    (hE : S e∈above wt (n+1)) (hzero : S (p+e)=0) :
    C p=0 ∧ T p∈strictlyBelow wt n := by
  have hSp : S p∈above wt (n+1) := by
    have h : S p= -S e := eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hzero)
    rw [h]
    exact (above wt (n+1)).neg_mem hE
  have hCp : C p∈above wt (n+1) := by
    have h : C p=S p-(S p-C p) := by abel
    rw [h]
    exact (above wt (n+1)).sub_mem hSp hSC
  have h := eq_zero_of_homogeneous_above wt n hC hCp
  exact ⟨h,by simpa only [h,sub_zero] using hTC⟩
end WordGrading

namespace AlphabetTransport
open AssociativeElimination WordGrading
variable {R α β : Type*} [CommRing R]

theorem map_homogeneous (e : α → β) (wa : α → ℕ) (wb : β → ℕ)
    (he : ∀ a,wb (e a)=wa a) {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    map e p∈homogeneous wb n := by
  apply algHom_homogeneous _ wa wb _ hp
  intro a
  rw [map_atom]
  exact word_mem (FreeMonoid.of (e a)) (by simp [he])

theorem map_above (e : α → β) (wa : α → ℕ) (wb : β → ℕ)
    (he : ∀ a,wb (e a)=wa a) {n : ℕ} {p : A R α} (hp : p∈above wa n) :
    map e p∈above wb n := by
  apply algHom_above _ wa wb _ hp
  intro a
  rw [map_atom]
  exact word_mem (FreeMonoid.of (e a)) (by simp [he])

end AlphabetTransport

namespace SecondStage
open AssociativeElimination WordGrading PolynomialOrdering

def fc : F → ℕ | 1 => 1 | _ => 0
def bc : B → ℕ := fun _ => 0
def count : E → ℕ := Sum.elim fc bc

theorem count_toOld (s : E) : CountTables.baseCount (toOld s)=count s := by
  cases s with
  | inl a => fin_cases a <;> rfl
  | inr a => rfl

theorem count_fromOld (a : Old) : count (fromOld a)=CountTables.baseCount a := by
  fin_cases a <;> rfl

theorem H_homo : H∈homogeneous fc 0 := word_mem (FreeMonoid.of 0) rfl
theorem U_homo : U∈homogeneous fc 1 := word_mem (FreeMonoid.of 1) rfl
theorem V_homo : V∈homogeneous fc 0 := word_mem (FreeMonoid.of 2) rfl
theorem bracket_homo {n m : ℕ} {p q : A K F}
    (hp : p∈homogeneous fc n) (hq : q∈homogeneous fc m) :
    bracket p q∈homogeneous fc (n+m) := by
  apply (homogeneous fc (n+m)).sub_mem (homogeneous_mul hp hq)
  simpa only [Nat.add_comm] using homogeneous_mul hq hp

theorem common_homo (b : B) (a : F) : common b a∈homogeneous fc (bc b+fc a) := by
  fin_cases a
  · exact bracket_homo H_homo V_homo
  · exact bracket_homo ((homogeneous fc 0).add_mem H_homo V_homo) U_homo
  · exact bracket_homo H_homo V_homo

theorem higher_homo (b : B) (a : F) : higher b a∈homogeneous fc (bc b+fc a+2) := by
  fin_cases a
  · have h := bracket_homo (bracket_homo H_homo U_homo) U_homo
    exact h
  · exact (homogeneous fc _).zero_mem
  · have h := bracket_homo (bracket_homo V_homo U_homo) U_homo
    exact h

theorem source_above (b : B) (a : F) : source b a∈above fc (bc b+fc a) := by
  apply (above fc _).add_mem (homogeneous_above (common_homo b a))
  exact space_mono (by intro w hw; change degree fc w=bc b+fc a+2 at hw; omega) (higher_homo b a)
theorem source_difference (b : B) (a : F) : source b a-common b a∈above fc (bc b+fc a+1) := by
  rw [source,add_sub_cancel_left]
  exact space_mono (by intro w hw; change degree fc w=bc b+fc a+2 at hw; omega) (higher_homo b a)

theorem order_common_homogeneous (n : ℕ) (p : A K Old)
    (hp : p∈homogeneous CountTables.baseCount n) : order common p∈homogeneous CountTables.baseCount n := by
  apply AlphabetTransport.map_homogeneous toOld count _ count_toOld
  apply merge_homogeneous fc bc
  apply normalize_homogeneous fc bc common_homo
  exact AlphabetTransport.map_homogeneous fromOld _ count count_fromOld hp

theorem order_source_above (n : ℕ) (p : A K Old)
    (hp : p∈above CountTables.baseCount n) : order source p∈above CountTables.baseCount n := by
  apply AlphabetTransport.map_above toOld count _ count_toOld
  apply merge_above fc bc
  apply normalize_above fc bc source_above
  exact AlphabetTransport.map_above fromOld _ count count_fromOld hp

theorem order_difference (n : ℕ) (p : A K Old)
    (hp : p∈homogeneous CountTables.baseCount n) :
    order source p-order common p∈above CountTables.baseCount (n+1) := by
  change outward (ordered source (inward p))-outward (ordered common (inward p))∈_
  rw [← map_sub]
  apply AlphabetTransport.map_above toOld count _ count_toOld
  exact (ordered_comparison_above fc bc common_homo source_above source_difference
    (AlphabetTransport.map_homogeneous fromOld _ count count_fromOld hp)).2

theorem order_common_below (n : ℕ) (p : A K Old)
    (hp : p∈below CountTables.baseCount n) : order common p∈below CountTables.baseCount n := by
  apply map_space (order common) _ ?_ hp
  intro w hw
  exact space_mono (by intro v hv; change degree CountTables.baseCount v=degree CountTables.baseCount w at hv; change degree CountTables.baseCount w≤n at hw; omega)
    (order_common_homogeneous _ _ (word_mem w rfl))

end SecondStage
namespace ExactCountOrdering
open AssociativeElimination WordGrading PolynomialOrdering

theorem source_comparison {n : ℕ} {p : A K E} (hp : p∈homogeneous count n) :
    C p∈homogeneous count n ∧ S p-C p∈above count (n+1) :=
  iterated_comparison_above CountTables.fiberCount CountTables.baseCount _ _
    SecondStage.order_common_homogeneous SecondStage.order_source_above SecondStage.order_difference
    CountTables.common_homo CountTables.source_above CountTables.source_difference hp

theorem target_comparison {n : ℕ} {p : A K E} (hp : p∈homogeneous count n) :
    C p∈homogeneous count n ∧ T p-C p∈strictlyBelow count n := by
  apply iterated_comparison_below CountTables.fiberCount CountTables.baseCount _ _
    SecondStage.order_common_homogeneous SecondStage.order_common_below _
    CountTables.common_homo CountTables.target_below CountTables.target_difference hp
  intro m q _
  rw [sub_self]
  exact (strictlyBelow CountTables.baseCount _).zero_mem

theorem source_above {n : ℕ} {p : A K E} (hp : p∈above count n) : S p∈above count n :=
  iterated_above CountTables.fiberCount CountTables.baseCount _ SecondStage.order_source_above
    CountTables.source_above hp

theorem transfer_oai (n : ℕ) (p e : A K E) (hp : p∈homogeneous count n)
    (he : e∈above count (n+1)) (hzero : S (p+e)=0) :
    C p=0 ∧ T p∈strictlyBelow count n := by
  obtain ⟨hC,hS⟩ := source_comparison hp
  exact count_transfer count S C T n p e hC hS (target_comparison hp).2 (source_above he) hzero
end ExactCountOrdering

end DeligneDrinfeld

end

end OAI

end




















section
open OAI.DeligneDrinfeld.ExactCountOrdering in
theorem solution : ∀ (n : ℕ)
    (p e :
      OAI.DeligneDrinfeld.AssociativeElimination.A OAI.DeligneDrinfeld.ExactCountOrdering.K
        OAI.DeligneDrinfeld.ExactCountOrdering.E)
    (hp : p ∈ OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.ExactCountOrdering.count n)
    (he : e ∈ OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.ExactCountOrdering.count (n + 1))
    (hzero : OAI.DeligneDrinfeld.ExactCountOrdering.S (p + e) = 0),
    OAI.DeligneDrinfeld.ExactCountOrdering.C p = 0 ∧
      OAI.DeligneDrinfeld.ExactCountOrdering.T p ∈
        OAI.DeligneDrinfeld.WordGrading.strictlyBelow OAI.DeligneDrinfeld.ExactCountOrdering.count n :=
  @OAI.DeligneDrinfeld.ExactCountOrdering.transfer_oai
end
