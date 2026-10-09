-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.weighted_kernel_sampling_defect
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-08T15:48:21.958839+00:00
-- url     : https://prove2.me/submissions/a0242a80-234d-4d51-9d48-9524568e8de3

import Mathlib
import Definitions.Def_SidorenkoWeightedKernelData

open scoped BigOperators
open OAI.SidorenkoCounterexample

namespace SidorenkoSamplingProof
open Classical

noncomputable def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card A : ℝ)

lemma uniformMean_congr {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

lemma uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, nsmul_eq_mul, ne_of_gt (Fintype.card_pos (α := A))]

lemma uniformMean_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp only [uniformMean, Finset.sum_sub_distrib, sub_div]

lemma uniformMean_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  unfold uniformMean
  rw [←Finset.mul_sum]
  ring

lemma uniformMean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![
  ![0,1,3], ![0,1,9], ![0,2,3], ![0,2,9], ![1,3,10], ![1,7,10],
  ![1,7,12], ![1,9,12], ![2,3,4], ![2,4,9], ![3,4,11], ![3,10,11],
  ![4,8,9], ![4,8,11], ![5,6,7], ![5,6,11], ![5,7,10], ![5,10,11],
  ![6,7,12], ![6,8,11], ![6,8,12], ![8,9,12]]

lemma faceVertex_correct : ∀ j : Fin 22,
    faces j = {faceVertex j 0, faceVertex j 1, faceVertex j 2} := by decide
lemma faceVertex_injective : ∀ j : Fin 22, Function.Injective (faceVertex j) := by decide
lemma faces_image : ∀ j : Fin 22, faces j = Finset.univ.image (faceVertex j) := by decide

lemma faceVertex_mem (j : Fin 22) (r : Fin 3) :
    H.Adj (.inl (faceVertex j r)) (.inr j) := by
  change faceVertex j r ∈ faces j
  rw [faceVertex_correct]
  fin_cases r <;> simp

abbrev ActCorner := Fin 22 × Fin 3
def cornerPoint (k : ActCorner) : Fin 13 := faceVertex k.1 k.2


structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a,0≤weight a
  total : ∑ a,weight a=1

namespace FiniteLaw
variable {A B C I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
noncomputable def mean (p : FiniteLaw A) (f : A → ℝ) : ℝ := ∑ a,p.weight a*f a

theorem mean_congr (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a=g a) : p.mean f=p.mean g := by
  unfold mean; exact Finset.sum_congr rfl fun a _ => congrArg (p.weight a*·) (h a)
@[simp] theorem mean_const (p : FiniteLaw A) (c : ℝ) : p.mean (fun _ => c)=c := by
  rw [mean,←Finset.sum_mul,p.total,one_mul]
theorem mean_add (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a+g a)=p.mean f+p.mean g := by simp only [mean,mul_add,Finset.sum_add_distrib]
theorem mean_sub (p : FiniteLaw A) (f g : A → ℝ) :
    p.mean (fun a => f a-g a)=p.mean f-p.mean g := by simp only [mean,mul_sub,Finset.sum_sub_distrib]
theorem mean_mul (p : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    p.mean (fun a => c*f a)=c*p.mean f := by unfold mean; rw [Finset.mul_sum]; congr 1; funext a; ring
theorem mean_mul_right (p : FiniteLaw A) (f : A → ℝ) (c : ℝ) :
    p.mean (fun a => f a*c)=p.mean f*c := by unfold mean; rw [Finset.sum_mul]; congr 1; funext a; ring
omit [DecidableEq I] in
theorem mean_sum (p : FiniteLaw A) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i,f i a)=∑ i,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
omit [Fintype I] [DecidableEq I] in
theorem mean_finset_sum (p : FiniteLaw A) (s : Finset I) (f : I → A → ℝ) :
    p.mean (fun a => ∑ i∈s,f i a)=∑ i∈s,p.mean (f i) := by unfold mean; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
theorem mean_nonneg (p : FiniteLaw A) {f : A → ℝ} (hf : ∀ a,0≤f a) : 0≤p.mean f :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) (hf a))
theorem mean_mono (p : FiniteLaw A) {f g : A → ℝ} (h : ∀ a,f a≤g a) : p.mean f≤p.mean g :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a))
theorem mean_bound (p : FiniteLaw A) {f : A → ℝ} {c : ℝ} (h : ∀ a,f a≤c) : p.mean f≤c := by
  simpa only [mean_const] using p.mean_mono h
theorem abs_mean_le (p : FiniteLaw A) (f : A → ℝ) : |p.mean f|≤p.mean (fun a => |f a|) := by
  calc
    _ ≤ ∑ a,|p.weight a*f a| := Finset.abs_sum_le_sum_abs ..
    _ = _ := by simp only [mean,abs_mul,abs_of_nonneg (p.nonneg _)]

noncomputable def dirac (a : A) : FiniteLaw A where
  weight b := if b=a then 1 else 0
  nonneg b := by split <;> norm_num
  total := by simp
@[simp] theorem mean_dirac (a : A) (f : A → ℝ) : (dirac a).mean f=f a := by simp [mean,dirac]

noncomputable def uniform [Nonempty A] : FiniteLaw A where
  weight _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [nsmul_eq_mul,ne_of_gt (Fintype.card_pos (α := A))]
theorem mean_uniform [Nonempty A] (f : A → ℝ) : uniform.mean f=uniformMean f := by
  simp only [mean,uniform,uniformMean,div_eq_mul_inv,Finset.sum_mul,mul_comm]

noncomputable def prod (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  weight x := p.weight x.1*q.weight x.2
  nonneg _ := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum,q.total,mul_one]; exact p.total
@[simp] theorem mean_prod (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ) :
    (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b))) := by
  unfold mean prod; rw [Fintype.sum_prod_type]; simp_rw [Finset.mul_sum,mul_assoc]

theorem mean_swap (p : FiniteLaw A) (q : FiniteLaw B) (f : A → B → ℝ) :
    p.mean (fun a => q.mean (f a))=q.mean (fun b => p.mean (fun a => f a b)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _; ring

noncomputable def independent (p : I → FiniteLaw A) : FiniteLaw (I → A) where
  weight x := ∏ i,(p i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (p i).nonneg (x i))
  total := by rw [←Fintype.prod_sum]; simp only [(p _).total,Finset.prod_const_one]

theorem independent_mean_product (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (independent p).mean (fun x => ∏ i,f i (x i))=∏ i,(p i).mean (f i) := by
  simp only [mean,independent,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i).weight a*f i a)).symm

theorem mean_map_product (p : I → FiniteLaw A) (f : I → A → ℝ) :
    (∏ i,(p i).mean (f i))=∑ x : I → A,∏ i,(p i).weight (x i)*f i (x i) := by
  simp only [mean,Fintype.prod_sum]

noncomputable def mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : FiniteLaw A where
  weight a := t*p.weight a+(1-t)*q.weight a
  nonneg a := add_nonneg (mul_nonneg ht (p.nonneg a)) (mul_nonneg (by linarith) (q.nonneg a))
  total := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,p.total,q.total]; ring

theorem mean_mixture (p q : FiniteLaw A) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) (f : A → ℝ) :
    (mixture p q t ht ht1).mean f=t*p.mean f+(1-t)*q.mean f := by
  unfold mean mixture; simp only [add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]

noncomputable def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B where
  weight b := ∑ a,if f a=b then p.weight a else 0
  nonneg b := Finset.sum_nonneg (fun a _ => by split <;> simp only [p.nonneg,le_refl])
  total := by rw [Finset.sum_comm]; simpa using p.total

theorem mean_map (p : FiniteLaw A) (f : A → B) (g : B → ℝ) :
    (p.map f).mean g=p.mean (g ∘ f) := by
  simp only [mean,map,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp


end FiniteLaw

section EquivLaw
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
lemma independent_mean_equiv {C : Type*} [Fintype C]
    (e : I ≃ J) (p : J → FiniteLaw C) (f : (J → C) → ℝ) :
    (FiniteLaw.independent (fun i => p (e i))).mean (fun x => f (fun j => x (e.symm j)))=
      (FiniteLaw.independent p).mean f := by
  unfold FiniteLaw.mean FiniteLaw.independent
  let E : (I → C) ≃ (J → C) := Equiv.arrowCongr e (Equiv.refl C)
  apply Fintype.sum_equiv E
  intro x
  dsimp [E]
  congr 1
  symm
  exact Fintype.prod_equiv e.symm _ _ (fun j => by simp)


end EquivLaw

namespace FiniteLaw
section Marginal
variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
lemma independent_mean_sum (p : I ⊕ J → FiniteLaw A) (f : (I ⊕ J → A) → ℝ) :
    (independent p).mean f=(independent (fun i => p (.inl i))).mean (fun x =>
      (independent (fun j => p (.inr j))).mean (fun y => f (Sum.elim x y))) := by
  unfold mean independent
  simp only [Finset.mul_sum]
  rw [←Fintype.sum_prod_type (fun xy : (I → A) × (J → A) =>
    (∏ i,(p (.inl i)).weight (xy.1 i))*((∏ j,(p (.inr j)).weight (xy.2 j))*f (Sum.elim xy.1 xy.2)))]
  apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J A)
  intro x
  simp only [Fintype.prod_sum_type,Equiv.sumArrowEquivProdArrow,Equiv.coe_fn_mk]
  have he : Sum.elim (fun i => x (.inl i)) (fun j => x (.inr j))=x := by funext ij; cases ij <;> rfl
  change _ = (∏ i,(p (.inl i)).weight (x (.inl i)))*
    ((∏ j,(p (.inr j)).weight (x (.inr j)))*f (Sum.elim (fun i => x (.inl i)) (fun j => x (.inr j))))
  rw [he]; ring
lemma independent_mean_injective (p : J → FiniteLaw A) (e : I → J) (he : Function.Injective e)
    (f : (I → A) → ℝ) :
    (independent p).mean (fun x => f (fun i => x (e i)))=(independent (fun i => p (e i))).mean f := by
  let E : I ⊕ {j : J // j∉Set.range e} ≃ J :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))
  have hE (i : I) : E (.inl i)=e i := rfl
  have h := independent_mean_equiv E p (fun x => f (fun i => x (e i)))
  rw [←h,independent_mean_sum]
  have hi (x : I → A) (y : {j : J // j∉Set.range e} → A) :
      (fun i => Sum.elim x y (E.symm (e i)))=x := by
    funext i; rw [←hE i,E.symm_apply_apply]; rfl
  simp only [hi,mean_const,hE]
noncomputable def bind (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw B where
  weight b := ∑ a,p.weight a*(q a).weight b
  nonneg b := Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))
  total := by rw [Finset.sum_comm]; simp_rw [←Finset.mul_sum,(q _).total,mul_one]; exact p.total
lemma mean_bind (p : FiniteLaw A) (q : A → FiniteLaw B) (f : B → ℝ) :
    (p.bind q).mean f=p.mean (fun a => (q a).mean f) := by
  simp only [mean,bind,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
lemma mean_pow_le (p : FiniteLaw A) (f : A → ℝ) (hf : ∀ a,0≤f a) (n : ℕ) :
    (p.mean f)^n≤p.mean (fun a => (f a)^n) := by
  simpa only [mean,smul_eq_mul] using (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := Finset.univ) (w := p.weight) (p := f) (fun a _ => p.nonneg a) p.total (fun a _ => hf a)
lemma exists_lt_of_mean_lt (p : FiniteLaw A) {f g : A → ℝ} (h : p.mean f<p.mean g) : ∃ a,f a<g a := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) (p.mean_mono hn)
end Marginal

end FiniteLaw

namespace FiniteLaw
lemma independent_uniform_mean {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (f : (I → A) → ℝ) : (independent (fun _ : I => (uniform : FiniteLaw A))).mean f=uniformMean f := by
  unfold mean independent uniform uniformMean
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,←inv_pow,←Finset.mul_sum,div_eq_mul_inv]
  ring

end FiniteLaw

section Kernel
variable {X Y : Type*} [Fintype X] [Fintype Y]
noncomputable def kernelMean (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  π.mean (fun x => ν.mean (W x))
noncomputable def bipartiteMoment (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  (FiniteLaw.independent (fun _ : Fin 13 => π)).mean (fun x =>
    (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun y =>
      ∏ k : ActCorner,W (x (cornerPoint k)) (y k.1)))
lemma bipartiteMoment_nonneg (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ)
    (hW : ∀ x y,0≤W x y) : 0≤bipartiteMoment π ν W :=
  FiniteLaw.mean_nonneg _ (fun _ => FiniteLaw.mean_nonneg _ (fun _ => Finset.prod_nonneg (fun _ _ => hW _ _)))

end Kernel

structure SamplingKernel where
  Ω : Type
  [finite : Fintype Ω]
  [nonempty : Nonempty Ω]
  law : FiniteLaw Ω
  value : Ω → Ω → ℝ
  nonneg : ∀ x y, 0 ≤ value x y
  le_one : ∀ x y, value x y ≤ 1
  symm : ∀ x y, value x y = value y x

attribute [instance] SamplingKernel.finite SamplingKernel.nonempty

noncomputable def fromWeighted (K : WeightedKernelData) : SamplingKernel where
  Ω := Fin K.size
  finite := inferInstance
  nonempty := ⟨⟨0, K.size_pos⟩⟩
  law := { weight := K.weight, nonneg := K.weight_nonneg, total := K.weight_total }
  value := K.value
  nonneg := K.value_nonneg
  le_one := K.value_le_one
  symm := K.value_symm


noncomputable def edgeIndicator {V : Type*} (G : SimpleGraph V) (a b : V) : ℝ := if G.Adj a b then 1 else 0
lemma edgeIndicator_nonneg {V : Type*} (G : SimpleGraph V) (a b : V) : 0≤edgeIndicator G a b := by
  unfold edgeIndicator; split <;> norm_num
lemma edgeIndicator_le_one {V : Type*} (G : SimpleGraph V) (a b : V) : edgeIndicator G a b≤1 := by
  unfold edgeIndicator; split <;> norm_num
lemma edgeIndicator_symm {V : Type*} (G : SimpleGraph V) (a b : V) : edgeIndicator G a b=edgeIndicator G b a := by
  simp only [edgeIndicator,G.adj_comm]
lemma mem_faces_iff (j : Fin 22) (i : Fin 13) : i∈faces j ↔ ∃ r,faceVertex j r=i := by
  rw [faceVertex_correct]
  constructor
  · simp only [Finset.mem_insert,Finset.mem_singleton] 
    rintro (h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  · rintro ⟨r,rfl⟩; fin_cases r <;> simp
lemma hom_iff_corners {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) :
    (∀ u v,H.Adj u v → G.Adj (f u) (f v)) ↔
      ∀ k : ActCorner,G.Adj (f (.inl (cornerPoint k))) (f (.inr k.1)) := by
  constructor
  · intro h k; exact h _ _ (faceVertex_mem k.1 k.2)
  · intro h u v huv
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim huv
      | inr j =>
        obtain ⟨r,hr⟩ := (mem_faces_iff j i).mp huv
        simpa only [cornerPoint,hr] using h (j,r)
    | inr j =>
      cases v with
      | inl i =>
        obtain ⟨r,hr⟩ := (mem_faces_iff j i).mp huv
        simpa only [cornerPoint,hr] using (h (j,r)).symm
      | inr j' => exact False.elim huv
noncomputable def homIndicator {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) : ℝ :=
  ∏ k : ActCorner,edgeIndicator G (f (.inl (cornerPoint k))) (f (.inr k.1))
lemma homIndicator_eq {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) :
    homIndicator G f=if ∀ u v,H.Adj u v → G.Adj (f u) (f v) then 1 else 0 := by
  simp only [homIndicator,edgeIndicator,Fintype.prod_boole,hom_iff_corners]
lemma homIndicator_nonneg {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) : 0≤homIndicator G f := by
  rw [homIndicator_eq]; split <;> norm_num
lemma homIndicator_le_one {V : Type*} (G : SimpleGraph V) (f : PatternVertex → V) : homIndicator G f≤1 := by
  rw [homIndicator_eq]; split <;> norm_num
lemma homDensity_eq_mean {V : Type*} [Fintype V] (G : SimpleGraph V) :
    homDensity H G=uniformMean (homIndicator G) := by
  unfold homDensity homCount uniformMean
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,homIndicator_eq,Nat.cast_pow]
  congr 1
  simp [Fintype.card_subtype]
lemma edgeDensity_eq_mean {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeDensity G=uniformMean (fun ab : V × V => edgeIndicator G ab.1 ab.2) := by
  have hs : (∑ a,∑ b,edgeIndicator G a b)=(2*(Fintype.card G.edgeSet) : ℕ) := by
    calc
      _ = ∑ a,(G.degree a : ℝ) := by
        apply Finset.sum_congr rfl; intro a _
        simp [edgeIndicator,←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter]
      _ = _ := by exact_mod_cast (G.sum_degrees_eq_twice_card_edges.trans (congrArg (2*·) G.edgeFinset_card))
  unfold edgeDensity uniformMean
  rw [Fintype.sum_prod_type,hs]
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Nat.cast_mul,Nat.cast_ofNat]
  congr 1; ring
lemma homDensity_nonneg {V : Type*} (G : SimpleGraph V) : 0≤homDensity H G := by
  unfold homDensity; positivity
lemma edgeDensity_nonneg {V : Type*} (G : SimpleGraph V) : 0≤edgeDensity G := by
  unfold edgeDensity; positivity
lemma edgeDensity_eq_zero_of_edgeless {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : ∀ a b,¬G.Adj a b) : edgeDensity G=0 := by
  rw [edgeDensity_eq_mean]; simp [uniformMean,edgeIndicator,h]
lemma sourceMoment_eq_bipartite {A : Type*} [Fintype A] (π : FiniteLaw A) (U : A → A → ℝ) :
    (FiniteLaw.independent (fun _ : PatternVertex => π)).mean (fun z =>
      ∏ k : ActCorner,U (z (.inl (cornerPoint k))) (z (.inr k.1)))=bipartiteMoment π π U := by
  rw [FiniteLaw.independent_mean_sum]; rfl

section SwapLaw
variable {A B : Type*} [Fintype A] [Fintype B]
lemma uniformMean_law_swap (p : FiniteLaw A) (f : A → B → ℝ) :
    uniformMean (fun b => p.mean (fun a => f a b))=p.mean (fun a => uniformMean (f a)) := by
  unfold uniformMean FiniteLaw.mean
  rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [←Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring


end SwapLaw

namespace FiniteLaw
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
lemma independent_mean_unit (p : FiniteLaw A) (f : A → ℝ) :
    (independent (fun _ : Unit => p)).mean (fun x => f (x ()))=p.mean f := by
  unfold mean independent
  apply Fintype.sum_equiv (Equiv.funUnique Unit A)
  intro x
  simp only [Fintype.prod_unique]; rfl
lemma independent_mean_apply (p : I → FiniteLaw A) (i : I) (f : A → ℝ) :
    (independent p).mean (fun x => f (x i))=(p i).mean f := by
  have h := independent_mean_injective p (fun _ : Unit => i) (fun _ _ _ => Subsingleton.elim _ _)
    (fun x => f (x ()))
  exact h.trans (independent_mean_unit (p i) f)
lemma independent_mean_two (p : FiniteLaw A) {i j : I} (hij : i≠j) (f : A → A → ℝ) :
    (independent (fun _ : I => p)).mean (fun x => f (x i) (x j))=p.mean (fun a => p.mean (f a)) := by
  let e : Unit ⊕ Unit → I := Sum.elim (fun _ => i) (fun _ => j)
  have he : Function.Injective e := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact (hij h).elim
    · exact (hij h.symm).elim
    · rfl
  have h := independent_mean_injective (fun _ : I => p) e he
    (fun x => f (x (.inl ())) (x (.inr ())))
  dsimp [e] at h
  rw [h,independent_mean_sum]
  change (independent (fun _ : Unit => p)).mean (fun x =>
    (independent (fun _ : Unit => p)).mean (fun y => f (x ()) (y ())))=_
  simp_rw [independent_mean_unit]
  exact independent_mean_unit p (fun a => p.mean (f a))
lemma uniform_mean_equal [Nonempty A] :
    (uniform : FiniteLaw A).mean (fun a => uniform.mean (fun b => if a=b then (1:ℝ) else 0))=
      (Fintype.card A : ℝ)⁻¹ := by
  have hi (a : A) : (uniform : FiniteLaw A).mean (fun b => if a=b then (1:ℝ) else 0)=(Fintype.card A : ℝ)⁻¹ := by
    simp [mean,uniform]
  simp only [hi,mean_const]
noncomputable def coin (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : FiniteLaw Bool :=
  mixture (dirac true) (dirac false) t ht ht1
noncomputable def boolValue (b : Bool) : ℝ := if b then 1 else 0
lemma boolValue_nonneg (b : Bool) : 0≤boolValue b := by cases b <;> norm_num [boolValue]
lemma boolValue_le_one (b : Bool) : boolValue b≤1 := by cases b <;> norm_num [boolValue]
lemma coin_mean (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : (coin t ht ht1).mean boolValue=t := by
  simp [coin,mean_mixture,boolValue]

end FiniteLaw

section Sample
variable {V : Type*} [Fintype V] [DecidableEq V]
def bitsGraph (b : Sym2 V → Bool) : SimpleGraph V where
  Adj x y := x≠y ∧ b s(x,y)=true
  symm.symm := by intro x y h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
  loopless.irrefl := by intro x h; exact h.1 rfl
omit [Fintype V] in
lemma bitsGraph_edgeIndicator (b : Sym2 V → Bool) (x y : V) :
    edgeIndicator (bitsGraph b) x y=if x=y then 0 else FiniteLaw.boolValue (b s(x,y)) := by
  by_cases h : x=y <;> simp [edgeIndicator,bitsGraph,FiniteLaw.boolValue,h]
noncomputable def edgeCoinLaw (U : SamplingKernel) (z : V → U.Ω) : FiniteLaw (Sym2 V → Bool) :=
  FiniteLaw.independent (fun e => FiniteLaw.coin
    (Sym2.lift ⟨fun a b => U.value (z a) (z b),fun a b => U.symm (z a) (z b)⟩ e)
    (by induction e using Sym2.inductionOn; exact U.nonneg _ _)
    (by induction e using Sym2.inductionOn; exact U.le_one _ _))
lemma edgeCoinLaw_mean (U : SamplingKernel) (z : V → U.Ω) (x y : V) :
    (edgeCoinLaw U z).mean (fun b => edgeIndicator (bitsGraph b) x y)=
      if x=y then 0 else U.value (z x) (z y) := by
  simp only [bitsGraph_edgeIndicator]
  by_cases h : x=y
  · simp [h]
  · simp only [h,ite_false,edgeCoinLaw]
    rw [FiniteLaw.independent_mean_apply,FiniteLaw.coin_mean]; rfl

end Sample

def cornerEdge (k : ActCorner) : Sym2 PatternVertex := s(Sum.inl (cornerPoint k),Sum.inr k.1)
lemma cornerEdge_injective : Function.Injective cornerEdge := by
  rintro ⟨j,r⟩ ⟨j',r'⟩ h
  simp only [cornerEdge,cornerPoint,Sym2.eq_iff,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,and_false,or_false] at h
  obtain ⟨h,hj⟩ := h
  subst j'
  exact congrArg (Prod.mk j) (faceVertex_injective j h)
section Random
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
lemma mappedCorner_injective (f : PatternVertex → V) (hf : Function.Injective f) :
    Function.Injective (fun k : ActCorner => s(f (.inl (cornerPoint k)),f (.inr k.1))) :=
  (Sym2.map.injective hf).comp cornerEdge_injective
omit [Fintype V] [DecidableEq V] in
lemma mappedCorner_ne (f : PatternVertex → V) (hf : Function.Injective f) (k : ActCorner) :
    f (.inl (cornerPoint k))≠f (.inr k.1) := by
  intro h; have hc := hf h; cases hc
lemma expectedHom_conditional (U : SamplingKernel) (z : V → U.Ω)
    (f : PatternVertex → V) (hf : Function.Injective f) :
    (edgeCoinLaw U z).mean (fun b => homIndicator (bitsGraph b) f)=
      ∏ k : ActCorner,U.value (z (f (.inl (cornerPoint k)))) (z (f (.inr k.1))) := by
  simp only [homIndicator,bitsGraph_edgeIndicator,mappedCorner_ne f hf,ite_false]
  unfold edgeCoinLaw
  rw [FiniteLaw.independent_mean_injective _ _ (mappedCorner_injective f hf)
    (fun b => ∏ k : ActCorner,FiniteLaw.boolValue (b k))]
  rw [FiniteLaw.independent_mean_product]
  apply Finset.prod_congr rfl; intro k _
  rw [FiniteLaw.coin_mean]; rfl
noncomputable def hostBitsLaw (U : SamplingKernel) : FiniteLaw (Sym2 V → Bool) :=
  (FiniteLaw.independent (fun _ : V => U.law)).bind (edgeCoinLaw U)
lemma expectedHom_injective (U : SamplingKernel) (f : PatternVertex → V) (hf : Function.Injective f) :
    (hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f)=bipartiteMoment U.law U.law U.value := by
  rw [hostBitsLaw,FiniteLaw.mean_bind]
  simp_rw [expectedHom_conditional U _ f hf]
  rw [FiniteLaw.independent_mean_injective _ _ hf (fun z =>
    ∏ k : ActCorner,U.value (z (.inl (cornerPoint k))) (z (.inr k.1)))]
  exact sourceMoment_eq_bipartite U.law U.value
lemma expectedEdge (U : SamplingKernel) (x y : V) :
    (hostBitsLaw U).mean (fun b => edgeIndicator (bitsGraph b) x y)=
      if x=y then 0 else kernelMean U.law U.law U.value := by
  rw [hostBitsLaw,FiniteLaw.mean_bind]
  simp_rw [edgeCoinLaw_mean]
  by_cases h : x=y
  · simp only [h,ite_true,FiniteLaw.mean_const]
  · simp only [h,ite_false]
    exact FiniteLaw.independent_mean_two U.law h U.value
lemma expectedHom_nonneg (U : SamplingKernel) (f : PatternVertex → V) :
    0≤(hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f) :=
  FiniteLaw.mean_nonneg _ (fun _b => homIndicator_nonneg _ _)
lemma expectedHom_le_one (U : SamplingKernel) (f : PatternVertex → V) :
    (hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f)≤1 :=
  FiniteLaw.mean_bound _ (fun _b => homIndicator_le_one _ _)
end Random

abbrev CollisionPair := {ab : Fin 35 × Fin 35 // ab.1<ab.2}
def sourceFinEquiv : PatternVertex ≃ Fin 35 := finSumFinEquiv
lemma collisionPair_card : Fintype.card CollisionPair=595 := by
  rw [Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin 35)))
  simpa only [Finset.univ_product_univ,Finset.card_univ,Fintype.card_fin,
    show Nat.choose 35 2=595 by decide] using h
noncomputable def collisionValue {V : Type*} (p : CollisionPair) (f : PatternVertex → V) : ℝ :=
  if f (sourceFinEquiv.symm p.1.1)=f (sourceFinEquiv.symm p.1.2) then 1 else 0
lemma collisionValue_nonneg {V : Type*} (p : CollisionPair) (f : PatternVertex → V) : 0≤collisionValue p f := by
  unfold collisionValue; split <;> norm_num
noncomputable def noninjectiveIndicator {V : Type*} (f : PatternVertex → V) : ℝ :=
  if Function.Injective f then 0 else 1
lemma noninjective_le_collisionSum {V : Type*} (f : PatternVertex → V) :
    noninjectiveIndicator f≤∑ p : CollisionPair,collisionValue p f := by
  unfold noninjectiveIndicator
  by_cases hf : Function.Injective f
  · simp only [hf,ite_true]; exact Finset.sum_nonneg (fun p _ => collisionValue_nonneg p f)
  · rw [if_neg hf]
    have hm : ∃ p : CollisionPair,f (sourceFinEquiv.symm p.1.1)=f (sourceFinEquiv.symm p.1.2) := by
      simp only [Function.Injective,not_forall] at hf
      obtain ⟨a,b,hfab,hne⟩ := hf
      rcases lt_or_gt_of_ne (fun h => hne (sourceFinEquiv.injective h)) with h|h
      · exact ⟨⟨(sourceFinEquiv a,sourceFinEquiv b),h⟩,by simpa using hfab⟩
      · exact ⟨⟨(sourceFinEquiv b,sourceFinEquiv a),h⟩,by simpa using hfab.symm⟩
    obtain ⟨p,hp⟩ := hm
    calc
      1 = collisionValue p f := by simp [collisionValue,hp]
      _ ≤ _ := Finset.single_le_sum (fun q _ => collisionValue_nonneg q f) (Finset.mem_univ p)
lemma collisionPair_ne (p : CollisionPair) : sourceFinEquiv.symm p.1.1≠sourceFinEquiv.symm p.1.2 :=
  fun h => (ne_of_lt p.2) (sourceFinEquiv.symm.injective h)
lemma collisionValue_mean {V : Type*} [Fintype V] [Nonempty V] (p : CollisionPair) :
    (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean (collisionValue p)=
      (Fintype.card V : ℝ)⁻¹ := by
  unfold collisionValue
  rw [FiniteLaw.independent_mean_two FiniteLaw.uniform (collisionPair_ne p) (fun a b : V => if a=b then (1:ℝ) else 0)]
  exact FiniteLaw.uniform_mean_equal
lemma noninjective_mean_bound {V : Type*} [Fintype V] [Nonempty V] :
    (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
      noninjectiveIndicator≤595/(Fintype.card V : ℝ) := by
  calc
    _ ≤ (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
        (fun f => ∑ p : CollisionPair,collisionValue p f) := FiniteLaw.mean_mono _ noninjective_le_collisionSum
    _ = _ := by
      rw [FiniteLaw.mean_sum]
      simp only [collisionValue_mean,Finset.sum_const,Finset.card_univ,collisionPair_card,nsmul_eq_mul]
      norm_num [div_eq_mul_inv]

section Bounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
lemma uniformMean_offdiag (c : ℝ) :
    uniformMean (fun ab : V × V => if ab.1=ab.2 then 0 else c)=(1-(Fintype.card V : ℝ)⁻¹)*c := by
  rw [uniformMean_prod]
  have hi (a : V) : uniformMean (fun b : V => if a=b then 0 else c)=(1-(Fintype.card V : ℝ)⁻¹)*c := by
    calc
      _ = uniformMean (fun b : V => c-c*(if a=b then (1:ℝ) else 0)) := by
        apply uniformMean_congr; intro b; split <;> simp_all
      _ = _ := by
        rw [uniformMean_sub,uniformMean_const,uniformMean_mul]
        simp [uniformMean]; ring
  simp only [hi,uniformMean_const]
lemma expectedEdgeDensity (U : SamplingKernel) :
    (hostBitsLaw U).mean (fun b : Sym2 V → Bool => edgeDensity (bitsGraph b))=
      (1-(Fintype.card V : ℝ)⁻¹)*kernelMean U.law U.law U.value := by
  simp_rw [edgeDensity_eq_mean]
  rw [←uniformMean_law_swap]
  simp_rw [expectedEdge]
  exact uniformMean_offdiag _
omit [Nonempty V] in
lemma expectedHom_map_bound (U : SamplingKernel) (f : PatternVertex → V) :
    (hostBitsLaw U).mean (fun b => homIndicator (bitsGraph b) f)≤
      bipartiteMoment U.law U.law U.value+noninjectiveIndicator f := by
  unfold noninjectiveIndicator
  by_cases hf : Function.Injective f
  · rw [if_pos hf,add_zero,expectedHom_injective U f hf]
  · rw [if_neg hf]
    have hτ := bipartiteMoment_nonneg U.law U.law U.value U.nonneg
    exact (expectedHom_le_one U f).trans (by linarith)
lemma expectedHomDensity_bound (U : SamplingKernel) :
    (hostBitsLaw U).mean (fun b : Sym2 V → Bool => homDensity H (bitsGraph b))≤
      bipartiteMoment U.law U.law U.value+595/(Fintype.card V : ℝ) := by
  simp_rw [homDensity_eq_mean]
  rw [←uniformMean_law_swap,←FiniteLaw.independent_uniform_mean]
  calc
    _ ≤ (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
        (fun f => bipartiteMoment U.law U.law U.value+noninjectiveIndicator f) :=
      FiniteLaw.mean_mono _ (expectedHom_map_bound U)
    _ = bipartiteMoment U.law U.law U.value+
        (FiniteLaw.independent (fun _ : PatternVertex => (FiniteLaw.uniform : FiniteLaw V))).mean
          noninjectiveIndicator := by rw [FiniteLaw.mean_add,FiniteLaw.mean_const]
    _ ≤ _ := add_le_add le_rfl (noninjective_mean_bound (V := V))

end Bounds


lemma kernelMean_fromWeighted (K : WeightedKernelData) :
    kernelMean (fromWeighted K).law (fromWeighted K).law (fromWeighted K).value =
      kernelEdgeMean K := by
  unfold kernelMean kernelEdgeMean FiniteLaw.mean fromWeighted
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma moment_fromWeighted (K : WeightedKernelData) :
    bipartiteMoment (fromWeighted K).law (fromWeighted K).law (fromWeighted K).value =
      kernelPatternMoment K := by
  rw [←sourceMoment_eq_bipartite]
  change (∑ f : PatternVertex → Fin K.size,
    (∏ v : PatternVertex, K.weight (f v)) *
      (∏ k : ActCorner, K.value (f (.inl (cornerPoint k))) (f (.inr k.1)))) = _
  unfold kernelPatternMoment
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [faces_image, Finset.prod_image (fun a _ b _ h => faceVertex_injective j h)]
  rfl

end SidorenkoSamplingProof

open SidorenkoSamplingProof

theorem solution (K : WeightedKernelData) (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∃ w : Fin m → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∃ G : Fin m → SimpleGraph (Fin n),
        (∑ i, w i * (homDensity H (G i) - (edgeDensity (G i)) ^ 66)) ≤
          kernelPatternMoment K + 595 / (n : ℝ) -
            ((1 - 1 / (n : ℝ)) * kernelEdgeMean K) ^ 66 := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let U := fromWeighted K
  let A := Sym2 (Fin n) → Bool
  let p : FiniteLaw A := hostBitsLaw U
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  have htotal : (∑ i : Fin (Fintype.card A), p.weight (e.symm i)) = 1 :=
    (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans p.total
  have hHom :
      p.mean (fun b => homDensity H (bitsGraph b)) ≤
        kernelPatternMoment K + 595 / (n : ℝ) := by
    simpa only [p, U, Fintype.card_fin, moment_fromWeighted] using
      (expectedHomDensity_bound (V := Fin n) U)
  have hEdge :
      p.mean (fun b => edgeDensity (bitsGraph b)) =
        (1 - 1 / (n : ℝ)) * kernelEdgeMean K := by
    simpa only [p, U, Fintype.card_fin, kernelMean_fromWeighted, one_div] using
      (expectedEdgeDensity (V := Fin n) U)
  have hJ :
      ((1 - 1 / (n : ℝ)) * kernelEdgeMean K) ^ 66 ≤
        p.mean (fun b => (edgeDensity (bitsGraph b)) ^ 66) := by
    rw [←hEdge]
    exact FiniteLaw.mean_pow_le p _ (fun b => edgeDensity_nonneg (bitsGraph b)) 66
  refine ⟨Fintype.card A, (fun i => p.weight (e.symm i)),
    (fun i => p.nonneg (e.symm i)), htotal, (fun i => bitsGraph (e.symm i)), ?_⟩
  have hequiv :
      (∑ i : Fin (Fintype.card A), p.weight (e.symm i) *
        (homDensity H (bitsGraph (e.symm i)) - (edgeDensity (bitsGraph (e.symm i))) ^ 66)) =
      p.mean (fun b => homDensity H (bitsGraph b) - (edgeDensity (bitsGraph b)) ^ 66) := by
    unfold FiniteLaw.mean
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  rw [hequiv, FiniteLaw.mean_sub]
  exact (sub_le_sub_right hHom _).trans (sub_le_sub_left hJ _)

