-- Prove2me | solution 1 for OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:04:27.041946+00:00
-- url     : https://prove2.me/submissions/399cb948-1e6f-4f29-995e-7599603b83ed

import Mathlib
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_HarmonicAnalysis_WordGeometry_exists_infinite_finiteDimensional_linear_image_bs
import Theorems.Thm_OAI_CriticalPercolation_HomogeneousAnalysis_Geometry_finite_stabilizer_harmonic_image_bs
import Theorems.Thm_OAI_CriticalPercolation_LinearGrowth_StrongFullSpan_virtually_comm_range_bs

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_PolynomialGrowthDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma finite_subset_word_ball (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (T : Finset A) :
    ∃ L : ℕ, T ⊆ S^L := by
  have hword : ∀ a : A, ∃ n : ℕ, a ∈ S^n := fun a =>
    exists_mem_pow S hsym (by rw [hgen]; trivial)
  choose l hl using hword
  refine ⟨T.sup l,fun a ha => ?_⟩
  exact Finset.pow_subset_pow_right h1 (Finset.le_sup ha) (hl a)

theorem degree_of_injective (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (f : B →* A) (hf : Injective f)
    (T : Finset B) (d : ℕ) (hg : HasDegree S d) : HasDegree T d := by
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hsym hgen (T.image f)
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hLpos : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hLpos).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hLpos
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    (T^n).card = ((T^n).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ = ((T.image f)^n).card := by rw [Finset.image_pow]
    _ ≤ ((S^L)^n).card := Finset.card_le_card (Finset.pow_subset_pow_left hL)
    _ = (S^(L*n)).card := by rw [pow_mul]
    _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 (by nlinarith))
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = C*(2*(L+1))^d*n^d := by rw [mul_pow,mul_assoc]

lemma hasPolynomialDegree_iff (d : ℕ) : HasPolynomialDegree A d ↔
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧
      Subgroup.closure (S : Set A)=⊤ ∧ HasDegree S d := by
  constructor
  · rintro ⟨S,hSf,h1,hsym,hgen,C,hC⟩
    refine ⟨hSf.toFinset,by simpa using h1,?_,by simpa using hgen,C,?_⟩
    · apply Finset.coe_injective
      simpa only [Finset.coe_inv,Set.Finite.coe_toFinset] using hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      refine ⟨n,hn,?_⟩
      have hb' : ((hSf.toFinset : Set A)^n).ncard ≤ C*n^d := by
        simpa only [Set.Finite.coe_toFinset] using hb
      simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb'
  · rintro ⟨S,h1,hsym,hgen,C,hC⟩
    refine ⟨S,S.finite_toSet,h1,?_,hgen,C,?_⟩
    · simpa only [Finset.coe_inv] using congrArg (fun T : Finset A => (T : Set A)) hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      exact ⟨n,hn,by simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb⟩

omit [DecidableEq A] in
lemma HasPolynomialDegree.fg {d : ℕ} (h : HasPolynomialDegree A d) : Group.FG A := by
  obtain ⟨S,hS,_,_,hgen,_⟩ := h
  exact Group.fg_iff.mpr ⟨S,hgen,hS⟩

lemma exists_symmetric_generators [Group.FG A] :
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure (S : Set A)=⊤ := by
  obtain ⟨F,hF⟩ := Group.FG.out (G := A)
  let S := insert 1 (F ∪ F⁻¹)
  refine ⟨S,by simp [S],?_,?_⟩
  · ext a
    simp only [S,Finset.mem_inv',Finset.mem_insert,Finset.mem_union,inv_eq_one,inv_inv]
    tauto
  · apply top_unique
    rw [← hF]
    apply Subgroup.closure_mono
    intro a ha
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)

theorem HasPolynomialDegree.of_injective {d : ℕ} (h : HasPolynomialDegree A d)
    (f : B →* A) (hf : Injective f) [Group.FG B] : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := B)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    degree_of_injective S h1 hs hgen f hf T d hg⟩

theorem HasPolynomialDegree.finiteIndex_subgroup {d : ℕ} (h : HasPolynomialDegree A d)
    (H : Subgroup A) [H.FiniteIndex] : HasPolynomialDegree H d := by
  let _ := h.fg
  exact h.of_injective H.subtype H.subtype_injective

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_NormalClosureGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma eventually_exponential_dominates (C k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, C*n^k < 2^n := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1:ℝ)<2)).const_mul (C:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (C:ℝ)*((n:ℝ)^k / 2^n) < 1 :=
    ht.eventually (Iio_mem_nhds (by simp : (C:ℝ)*0 < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hx := hN n hn
  rw [← mul_div_assoc] at hx
  have hx' := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mp hx
  exact_mod_cast hx'

lemma not_quadratic_exponential_lower (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (S^(L*n^2)).card) : False := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨N,hN⟩ := eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (S^(L*n^2)).card := hlo n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

lemma binaryProducts_mem (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) :
    ∀ n, ∀ x ∈ binaryProducts g n, x∈K n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have he : x=1 := by simpa [binaryProducts] using hx
    exact he ▸ (K 0).one_mem
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hK (Nat.le_succ n) (ih x hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (K (n+1)).mul_mem (hg n) (hK (Nat.le_succ n) (ih y hy))

lemma binaryProducts_card (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) (hout : ∀ n, g n∉K n) :
    ∀ n, (binaryProducts g n).card=2^n := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    have hd : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
      have hxK := binaryProducts_mem K hK g hg n x hx
      have hyK := binaryProducts_mem K hK g hg n y hy
      apply hout n
      rw [←he] at hxK
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using
        (K n).mul_mem hxK ((K n).inv_mem hyK)
    rw [binaryProducts,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (mul_right_injective (g n)),ih,pow_succ]
    omega

lemma binaryProducts_subset_pow (S : Finset A) (h1 : (1:A)∈S)
    (g : ℕ → A) (L : ℕ) (hg : ∀ n, g n∈S^(L*(n+1))) :
    ∀ n, binaryProducts g n ⊆ S^(L*n^2) := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L (Nat.pow_le_pow_left (Nat.le_succ n) 2)) (ih hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hlen : L*(n+1)+L*n^2 ≤ L*(n+1)^2 := by
        calc
          _ = L*(n+1+n^2) := by ring
          _ ≤ L*(n+1)^2 := Nat.mul_le_mul_left L (by nlinarith)
      apply Finset.pow_subset_pow_right h1 hlen
      rw [pow_add]
      exact Finset.mul_mem_mul (hg n) (ih hy)

theorem no_linear_word_strict_chain (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hgin : ∀ n, g n∈K (n+1)) (hgout : ∀ n, g n∉K n)
    (L : ℕ) (hL : 0<L) (hword : ∀ n, g n∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  rw [←binaryProducts_card K hK g hgin hgout n]
  exact Finset.card_le_card (binaryProducts_subset_pow S h1 g L hword n)

lemma mem_boundedConjugates (S F : Finset A) (n : ℕ) {x : A} :
    x∈boundedConjugates S F n ↔ ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x := by
  simp [boundedConjugates, MulAut.conj_apply]

lemma boundedConjugates_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (boundedConjugates S F) := by
  intro m n h x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F m).mp hx
  exact (mem_boundedConjugates S F n).mpr
    ⟨g,Finset.pow_subset_pow_right h1 h hg,f,hf,rfl⟩

lemma conjugateStage_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (conjugateStage S F) := by
  intro m n h
  exact Subgroup.closure_mono (boundedConjugates_mono S F h1 h)

lemma boundedConjugates_subset_pow (S F : Finset A) (hsym : S⁻¹=S)
    (L : ℕ) (hF : F⊆S^L) (n : ℕ) :
    boundedConjugates S F n ⊆ S^(2*n+L) := by
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  have hgi : g⁻¹∈S^n := by
    rw [←hsym,inv_pow]
    exact Finset.inv_mem_inv hg
  have he : 2*n+L=n+L+n := by omega
  rw [he,pow_add,pow_add]
  exact Finset.mul_mem_mul (Finset.mul_mem_mul hg (hF hf)) hgi

lemma conjugateStage_le_normalClosure (S F : Finset A) (n : ℕ) :
    conjugateStage S F n ≤ Subgroup.normalClosure (F : Set A) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  exact Subgroup.normalClosure_normal.conj_mem f (Subgroup.subset_normalClosure hf) g

lemma conjugateStage_conj_generator (S F : Finset A) (n : ℕ)
    (s : A) (hs : s∈S) {x : A} (hx : x∈conjugateStage S F n) :
    s*x*s⁻¹∈conjugateStage S F (n+1) := by
  change x∈Subgroup.closure _ at hx
  have hmap : conjugateStage S F n ≤
      (conjugateStage S F (n+1)).comap (MulAut.conj s) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hy
    apply Subgroup.subset_closure
    apply (mem_boundedConjugates S F (n+1)).mpr
    refine ⟨s*g,?_,f,hf,?_⟩
    · rw [pow_succ']
      exact Finset.mul_mem_mul hs hg
    · simp [MulAut.conj_apply,mul_assoc]
  exact hmap hx

lemma conjugateStage_normal_of_stationary (S F : Finset A) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (n : ℕ)
    (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    (conjugateStage S F n).Normal := by
  rw [←Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  change ∀ x, x∈conjugateStage S F n ↔ s*x*s⁻¹∈conjugateStage S F n
  intro x
  constructor
  · intro hx
    rw [←he]
    exact conjugateStage_conj_generator S F n s hs hx
  · intro hx
    have hsi : s⁻¹∈S := by rw [←hsym]; exact Finset.inv_mem_inv hs
    have hy := conjugateStage_conj_generator S F n s⁻¹ hsi hx
    rw [he] at hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hy

lemma normalClosure_eq_conjugateStage_of_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (n : ℕ) (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    Subgroup.normalClosure (F : Set A)=conjugateStage S F n := by
  let _ := conjugateStage_normal_of_stationary S F hsym hgen n he
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro f hf
    apply Subgroup.subset_closure
    exact (mem_boundedConjugates S F n).mpr
      ⟨1,Finset.one_mem_pow h1,f,hf,by simp⟩
  · exact conjugateStage_le_normalClosure S F n

theorem exists_conjugateStage_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (d : ℕ) (hg : HasDegree S d)
    (L : ℕ) (hF : F⊆S^L) :
    ∃ n : ℕ, conjugateStage S F (n+1)=conjugateStage S F n := by
  by_contra! hn
  have hw : ∀ n : ℕ, ∃ x∈boundedConjugates S F (n+1), x∉conjugateStage S F n := by
    intro n
    by_contra! h
    apply hn n
    apply le_antisymm ((Subgroup.closure_le _).mpr h)
    exact conjugateStage_mono S F h1 (Nat.le_succ n)
  choose g hgin hgout using hw
  apply no_linear_word_strict_chain S h1 d hg (conjugateStage S F)
    (conjugateStage_mono S F h1) g (fun n => Subgroup.subset_closure (hgin n))
    hgout (L+2) (by omega)
  intro n
  apply Finset.pow_subset_pow_right h1 (show 2*(n+1)+L≤(L+2)*(n+1) by nlinarith)
  exact boundedConjugates_subset_pow S F hsym L hF (n+1) (hgin n)

theorem normalClosure_fg_of_sparse_growth (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (d : ℕ) (hg : HasDegree S d) : (Subgroup.normalClosure (F : Set A)).FG := by
  obtain ⟨L,hF⟩ := finite_subset_word_ball S h1 hsym hgen F
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S F h1 hsym d hg L hF
  rw [normalClosure_eq_conjugateStage_of_stationary S F h1 hsym hgen n hn]
  exact (Subgroup.fg_iff _).mpr ⟨(boundedConjugates S F n : Set A),rfl,Finset.finite_toSet _⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_SolvableGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A]

omit [DecidableEq A] in
lemma isMulCommutative_of_generators (S : Set A) (hgen : Subgroup.closure S=⊤)
    (hcomm : ∀ x∈S, ∀ y∈S, x*y=y*x) : IsMulCommutative A := by
  have hc := Subgroup.isMulCommutative_closure
    (fun left hleft right hright => hcomm left hleft right hright)
  rw [hgen] at hc
  let _ := hc
  exact ⟨⟨fun x y => congrArg Subtype.val
    (mul_comm' (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup A))
      (⟨y,Subgroup.mem_top y⟩ : (⊤ : Subgroup A)))⟩⟩

lemma commutator_eq_normalClosure_generators (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤) :
    commutator A = Subgroup.normalClosure
      (((S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)) : Set A) := by
  let F := (S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)
  let N := Subgroup.normalClosure (F : Set A)
  change commutator A=N
  apply le_antisymm
  · apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    let q := QuotientGroup.mk' N
    apply isMulCommutative_of_generators (q '' (S : Set A))
    · rw [←MonoidHom.map_closure,hgen,←MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply (QuotientGroup.eq_one_iff ⁅x,y⁆).mpr
      apply Subgroup.subset_normalClosure
      exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hx
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

theorem HasPolynomialDegree.commutator_fg {d : ℕ} (h : HasPolynomialDegree A d) :
    (commutator A).FG := by
  obtain ⟨S,h1,hsym,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  rw [commutator_eq_normalClosure_generators S hgen]
  exact normalClosure_fg_of_sparse_growth S _ h1 hsym hgen d hg

omit [DecidableEq A] in
lemma map_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator A) n).map (commutator A).subtype =
      derivedSeries A (n+1) := by
  induction n with
  | zero =>
    change (⊤ : Subgroup (commutator A)).map (commutator A).subtype=commutator A
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  | succ n ih =>
    change (⁅derivedSeries (commutator A) n,derivedSeries (commutator A) n⁆).map _=_
    rw [Subgroup.map_commutator,ih]
    rfl

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_AbelianAlternatives
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical DirectSum

namespace CriticalPercolation

theorem additive_abelian_alternatives (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Finite A ∨
      (∃ φ : A →+ ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →+ (ℤ×ℤ), Surjective φ) := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  cases n with
  | zero =>
    exact Or.inl (Finite.of_equiv _ f.symm.toEquiv)
  | succ n =>
    cases n with
    | zero =>
      let φ := (Finsupp.applyAddHom (0 : Fin 1)).comp
        ((AddMonoidHom.fst (Fin 1 →₀ ℤ) T).comp f.toAddMonoidHom)
      have hs : Surjective φ := by
        intro z
        refine ⟨f.symm (Finsupp.single 0 z,0),?_⟩
        simp [φ]
      have hk : (φ.ker : Set A).Finite := by
        apply (Set.finite_singleton (0 : Fin 1 →₀ ℤ)).prod (Set.toFinite (Set.univ : Set T)) |>.preimage f.injective.injOn |>.subset
        intro x hx
        change (f x).1∈({0} : Set (Fin 1 →₀ ℤ)) ∧ (f x).2∈(Set.univ : Set T)
        refine ⟨?_,Set.mem_univ _⟩
        apply Finsupp.ext
        intro i
        have hi : i=(0 : Fin 1) := Fin.ext (by omega)
        subst i
        exact hx
      exact Or.inr (Or.inl ⟨φ,hs,hk⟩)
    | succ n =>
      let ev : (Fin (n+2) →₀ ℤ) →+ (ℤ×ℤ) :=
        (Finsupp.applyAddHom ⟨0,by omega⟩).prod (Finsupp.applyAddHom ⟨1,by omega⟩)
      let φ := ev.comp ((AddMonoidHom.fst (Fin (n+2) →₀ ℤ) T).comp f.toAddMonoidHom)
      refine Or.inr (Or.inr ⟨φ,?_⟩)
      intro z
      refine ⟨f.symm (Finsupp.single ⟨0,by omega⟩ z.1 +
        Finsupp.single ⟨1,by omega⟩ z.2,0),?_⟩
      simp [φ,ev]

theorem abelian_alternatives (A : Type*) [CommGroup A] [Group.FG A] :
    Finite A ∨
      (∃ φ : A →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  rcases additive_abelian_alternatives (Additive A) with h | ⟨φ,hs,hk⟩ | ⟨φ,hs⟩
  · let _ := h
    exact Or.inl (Finite.of_equiv _ Additive.toMul)
  · refine Or.inr (Or.inl ⟨φ.toMultiplicativeRight,?_,?_⟩)
    · exact fun z => hs z.toAdd
    · exact hk
  · refine Or.inr (Or.inr ⟨φ.toMultiplicativeRight,?_⟩)
    exact fun z => hs z.toAdd

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_VirtualIndicability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth

lemma infinite_fg_abelian_surjects_int (B : Type*) [CommGroup B] [Group.FG B]
    [Infinite B] : ∃ f : B →* Multiplicative ℤ, Surjective f := by
  rcases abelian_alternatives B with hf | ⟨f,hf,_⟩ | ⟨f,hf⟩
  · let _ := hf
    exact False.elim (_root_.not_finite B)
  · exact ⟨f,hf⟩
  · let p : Multiplicative (ℤ×ℤ) →* Multiplicative ℤ :=
      (AddMonoidHom.fst ℤ ℤ).toMultiplicative
    have hp : Surjective p := fun z => ⟨Multiplicative.ofAdd (z.toAdd,0),rfl⟩
    exact ⟨p.comp f,hp.comp hf⟩

lemma virtually_indicable_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → derivedSeries A n=⊥ → Infinite A →
      ∃ H : Subgroup A, H.FiniteIndex ∧
        ∃ f : H →* Multiplicative ℤ, Surjective f := by
  induction n with
  | zero =>
    intro A _ _ d hg hz hi
    have hs : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by simpa only [hz,Subgroup.mem_bot] using
        (show x∈derivedSeries A 0 from Subgroup.mem_top x)
      have hy : y=1 := by simpa only [hz,Subgroup.mem_bot] using
        (show y∈derivedSeries A 0 from Subgroup.mem_top y)
      exact hx.trans hy.symm
    exact False.elim (_root_.not_finite A)
  | succ n ih =>
    intro A _ _ d hg hz hi
    let _ := hg.fg
    let C := commutator A
    let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr hg.commutator_fg
    let Q := A ⧸ C
    let _ : IsMulCommutative Q :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
    rcases finite_or_infinite Q with hq | hq
    · let _ := hq
      let _ : C.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      have hc : Infinite C := by
        rcases finite_or_infinite C with hfin | hinf
        · let _ := hfin
          let _ : Finite A := (C.finite_iff_finite_and_finiteIndex).mpr ⟨hfin,inferInstance⟩
          exact False.elim (_root_.not_finite A)
        · exact hinf
      have hgC := hg.of_injective C.subtype Subtype.val_injective
      have hzC : derivedSeries C n=⊥ := by
        apply Subgroup.map_injective (f := C.subtype) Subtype.val_injective
        rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
      obtain ⟨H,hHi,f,hf⟩ := ih C d hgC hzC hc
      let _ := hHi
      let J := H.map C.subtype
      let e : H ≃* J := H.equivMapOfInjective C.subtype Subtype.val_injective
      have hJi : J.FiniteIndex := by
        constructor
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero hHi.index_ne_zero (inferInstance : C.FiniteIndex).index_ne_zero
      exact ⟨J,hJi,f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective⟩
    · let _ := hq
      obtain ⟨f,hf⟩ := infinite_fg_abelian_surjects_int Q
      let e : (⊤ : Subgroup A) ≃* A := Subgroup.topEquiv
      exact ⟨⊤,inferInstance,(f.comp (QuotientGroup.mk' C)).comp e.toMonoidHom,
        hf.comp ((QuotientGroup.mk'_surjective C).comp e.surjective)⟩

theorem HasPolynomialDegree.virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Group.IsSolvable A] [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact virtually_indicable_of_derivedSeries_eq_bot n A d hg hn inferInstance

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteCoverSums
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {I X : Type*}

lemma finite_incidence_sum (J : Finset I) (L : I → Finset X) (B : Finset X)
    (hsub : ∀ j∈J, L j⊆B) (f : X → ℝ) :
    (∑ j∈J, ∑ x∈L j, f x) =
      ∑ x∈B, ((J.filter (fun j => x∈L j)).card:ℝ)*f x := by
  have he (j : I) (hj : j∈J) : (∑ x∈L j, f x)=∑ x∈B, if x∈L j then f x else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨hsub j hj hx,hx⟩,fun hx => hx.2⟩
  calc
    _ = ∑ j∈J, ∑ x∈B, if x∈L j then f x else 0 := Finset.sum_congr rfl he
    _ = ∑ x∈B, ∑ j∈J, if x∈L j then f x else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [←Finset.sum_filter]
      simp

lemma sum_le_sum_of_finite_overlap (J : Finset I) (L : I → Finset X)
    (B : Finset X) (hsub : ∀ j∈J, L j⊆B) (K : ℕ)
    (hover : ∀ x∈B, (J.filter (fun j => x∈L j)).card≤K)
    (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ j∈J, ∑ x∈L j, f x)≤(K:ℝ)*(∑ x∈B, f x) := by
  rw [finite_incidence_sum J L B hsub f,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hover x hx)) (hf x)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma reachBall_self (o : X) (r : ℕ) : o∈reachBall Γ o r :=
  ⟨SimpleGraph.Walk.nil,Nat.zero_le _⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetBounded
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma Bounded.mul {S T U : Set A} (hT : Bounded S T) (hU : Bounded S U) : Bounded S (T*U) := by
  obtain ⟨n,hn⟩ := hT; obtain ⟨m,hm⟩ := hU
  exact ⟨n+m,by rw [pow_add]; exact Set.mul_subset_mul hn hm⟩

lemma finite_coset_image_iff_cover (K : Subgroup A) (T : Set A) :
    ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite ↔
      ∃ F : Set A, F.Finite ∧ T⊆F*(K:Set A) := by
  constructor
  · intro hf
    let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
    have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
    choose a ha he using hh
    let F := Set.range (fun q : Q => a q.val q.property)
    let : Finite Q := hf.to_subtype
    refine ⟨F,Set.finite_range _,?_⟩
    intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)
  · rintro ⟨F,hF,hcov⟩
    apply (hF.image (QuotientGroup.mk : A → A ⧸ K)).subset
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨f,hf,k,hk,rfl⟩ := hcov ht
    exact ⟨f,hf,QuotientGroup.eq.mpr (by simpa using hk)⟩

lemma HasDegree.bounded_generators {K : Subgroup A} {S T : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hg : HasDegree K S d) (hT : Bounded S T) : HasDegree K T d := by
  obtain ⟨L,hL⟩ := hT
  have hin (n : ℕ) : T^n⊆S^((L+1)*n) := by
    rw [pow_mul]
    exact Set.pow_subset_pow_left (hL.trans (Set.pow_subset_pow_right h1 (Nat.le_succ L)))
  refine ⟨fun n => (hg.1 _).subset (Set.image_mono (hin n)),?_⟩
  obtain ⟨C,hC⟩ := hg.2
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le (by omega : 0<L+1)).mpr (by simpa [Nat.mul_comm] using hr)
  have hnr : (L+1)*n ≤ r := by simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r (by omega : 0<L+1)
    change r<(L+1)*(n+1) at hlt
    have hh : 1≤n := (le_max_right R 1).trans hn
    nlinarith
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    _ ≤ (ball K S r).ncard := Set.ncard_le_ncard
      (Set.image_mono ((hin n).trans (Set.pow_subset_pow_right h1 hnr))) (hg.1 r)
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = _ := by rw [mul_pow]; ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_HomogeneousGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis

namespace Geometry
variable {X : Type*} (W : Geometry X)

lemma self_mem_around (x : X) (r : ℕ) : x∈W.around x r :=
  W.mem_around.mpr (GraphTopology.reachBall_self W.graph x r)

lemma exists_mem_ball (x : X) : ∃ n, x∈W.ball n := by
  obtain ⟨p,hp,he⟩ := W.connected.exists_path_of_dist W.root x
  exact ⟨p.length,W.mem_around.mpr ⟨p,le_rfl⟩⟩

lemma neighbors_card (x : X) : (W.neighbors x).card=(W.neighbors W.root).card := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.neighbors_image]
  exact Finset.card_image_of_injective _ g.injective

end Geometry
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

namespace Presentation
variable (P : Presentation A)

lemma walk_endpoint {x y : P.X} (p : P.graph.Walk x y) :
    ∀ g : A, P.projection g=x → ∃ h∈P.S^p.length, P.projection (g*h)=y := by
  induction p with
  | nil => intro g hg; exact ⟨1,by simp,by simpa using hg⟩
  | @cons x y z h p ih =>
    intro g hg
    obtain ⟨_,s,hs,he⟩ := (P.adj_mk_iff g y).mp (hg ▸ h)
    obtain ⟨t,ht,hz⟩ := ih (g*s) he
    refine ⟨s*t,?_,?_⟩
    · rw [SimpleGraph.Walk.length_cons,pow_succ']
      exact Set.mul_mem_mul hs ht
    · simpa only [mul_assoc] using hz
lemma reachBall_subset (n : ℕ) : GraphTopology.reachBall P.graph P.root n⊆ball P.K P.S n := by
  rintro y ⟨p,hp⟩
  obtain ⟨h,hh,he⟩ := P.walk_endpoint p 1 rfl
  exact ⟨h,Set.pow_subset_pow_right P.one_mem hp hh,by simpa using he⟩
lemma geometry_hasDegree (d : ℕ) (hg : HasDegree P.K P.S d) :
    (P.geometry (hg.1 1)).HasDegree d := by
  obtain ⟨hf,C,hC⟩ := hg
  refine ⟨C,?_⟩
  intro R
  obtain ⟨n,hn,hbound⟩ := hC R
  refine ⟨n,hn,?_⟩
  have hs : ((P.geometry (hf 1)).ball n : Set P.X)⊆ball P.K P.S n := by
    intro y hy
    exact P.reachBall_subset n ((P.geometry (hf 1)).mem_around.mp hy)
  have hc := Set.ncard_le_ncard hs (hf n)
  rw [Set.ncard_coe_finset] at hc
  exact hc.trans hbound

end Presentation
end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetTransfer
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma finite_image_of_finite_coset_image {B : Type*} [Group B]
    (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).Finite := by
  obtain ⟨F,hF,hcov⟩ := (finite_coset_image_iff_cover K T).mp hT
  apply ((hF.image f).mul hK).subset
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
  rw [map_mul]
  exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetImageGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma exists_finite_coset_cover (K : Subgroup A) (T : Set A)
    (hf : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    ∃ F : Set A, F.Finite ∧ F.ncard=((QuotientGroup.mk : A → A ⧸ K) '' T).ncard ∧ T⊆F*(K:Set A) := by
  let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
  have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
  choose a ha he using hh
  let F := Set.range (fun q : Q => a q.val q.property)
  let : Finite Q := hf.to_subtype
  have hi : Injective (fun q : Q => a q.val q.property) := by
    intro q r h
    apply Subtype.ext
    rw [←he q.val q.property,←he r.val r.property]
    exact congrArg (QuotientGroup.mk : A → A ⧸ K) h
  refine ⟨F,Set.finite_range _,?_,?_⟩
  · rw [Set.ncard_range_of_injective hi]
    rfl
  · intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)

lemma image_ncard_bound (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).ncard≤((QuotientGroup.mk : A → A ⧸ K) '' T).ncard*(f '' (K:Set A)).ncard := by
  obtain ⟨F,hF,hFc,hcov⟩ := exists_finite_coset_cover K T hT
  have hs : f '' T⊆(f '' F)*(f '' (K:Set A)) := by
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
    rw [map_mul]
    exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩
  calc
    _ ≤ ((f '' F)*(f '' (K:Set A))).ncard := Set.ncard_le_ncard hs ((hF.image f).mul hK)
    _ ≤ (f '' F).ncard*(f '' (K:Set A)).ncard := by
      have hh := @Finset.card_mul_le B _ _ (hF.image f).toFinset hK.toFinset
      simpa only [←Set.ncard_coe_finset,Finset.coe_mul,Set.Finite.coe_toFinset] using hh
    _ ≤ F.ncard*(f '' (K:Set A)).ncard := Nat.mul_le_mul_right _ (Set.ncard_image_le hF)
    _ = _ := by rw [hFc]

lemma HasDegree.image_polynomial {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (f : A →* B) (hf : Surjective f) (hK : (f '' (K:Set A)).Finite) :
    SparseGrowth.HasPolynomialDegree B d := by
  have hSf : (f '' S).Finite := finite_image_of_finite_coset_image K f hK S (by simpa only [ball,pow_one] using hg.1 1)
  refine ⟨f '' S,hSf,⟨1,h1,map_one f⟩,?_,?_,?_,?_⟩
  · rw [←Set.image_inv,hi]
  · rw [←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · exact hg.2.choose*(f '' (K:Set A)).ncard
  · intro R
    obtain ⟨n,hn,hb⟩ := hg.2.choose_spec R
    refine ⟨n,hn,?_⟩
    rw [←Set.image_pow]
    calc
      _ ≤ (ball K S n).ncard*(f '' (K:Set A)).ncard := image_ncard_bound K f hK (S^n) (hg.1 n)
      _ ≤ (hg.2.choose*n^d)*(f '' (K:Set A)).ncard := Nat.mul_le_mul_right _ hb
      _ = _ := by ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetPresentation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma normalized_generators (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) :
    ∃ P : Presentation A, P.K=K ∧ Bounded S P.S ∧ S⊆P.S := by
  let T := (K:Set A)*S*(K:Set A)
  have hs : S⊆T := by
    intro s hs
    have hh := Set.mul_mem_mul (Set.mul_mem_mul K.one_mem hs) K.one_mem
    simpa only [one_mul,mul_one] using hh
  have hT1 : (1:A)∈T := hs h1
  have hTi : T⁻¹=T := by
    dsimp [T]
    rw [mul_inv_rev,mul_inv_rev,inv_coe_set,hi,mul_assoc]
  have hTgen : Subgroup.closure T=⊤ := top_unique (hgen ▸ Subgroup.closure_mono hs)
  have hleft : (K:Set A)*T⊆T := by
    rintro _ ⟨k,hk,_,⟨_,⟨l,hl,s,hs,rfl⟩,m,hm,rfl⟩,rfl⟩
    have hh := Set.mul_mem_mul (Set.mul_mem_mul (K.mul_mem hk hl) hs) hm
    simpa only [T,mul_assoc] using hh
  refine ⟨⟨K,T,hT1,hTi,hTgen,hleft⟩,rfl,?_,hs⟩
  exact (hK.mul ⟨1,by simp⟩).mul hK

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_RealSparseDoubling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.HarmonicAnalysis

lemma sparse_real_doubling (f : ℕ → ℝ) (hf : Monotone f)
    (R₀ : ℕ) (hpos : ∀ n≥R₀, 0<f n) (C : ℝ) (hC : 0≤C)
    (d b : ℕ) (hb : 2≤b) (hpoly : ∀ R, ∃ n≥R, f n≤C*(n:ℝ)^d) :
    ∀ R : ℕ, ∃ n≥max R R₀, f (b*n)≤(b:ℝ)^(d+1)*f n := by
  intro R
  by_contra! hbad
  let a := max (max R R₀) 1
  have ha : 0<a := by dsimp [a]; omega
  have haR : max R R₀≤a := le_max_left _ _
  have hfapos : 0<f a := hpos a ((le_max_right R R₀).trans haR)
  have hgrow : ∀ k : ℕ, ((b:ℝ)^(d+1))^k*f a≤f (b^k*a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hr : max R R₀≤b^k*a := haR.trans (by
        have hh : 1≤b^k := Nat.one_le_pow k b (by omega)
        nlinarith)
      have hh := (hbad (b^k*a) hr).le
      calc
        _ = (b:ℝ)^(d+1)*(((b:ℝ)^(d+1))^k*f a) := by rw [pow_succ]; ring
        _ ≤ (b:ℝ)^(d+1)*f (b^k*a) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ f (b*(b^k*a)) := hh
        _ = _ := by congr 1; rw [pow_succ]; ring
  obtain ⟨N,hN⟩ := exists_nat_gt (C*((b*a:ℕ):ℝ)^d/f a)
  have hNF : C*((b*a:ℕ):ℝ)^d<(N:ℝ)*f a := (div_lt_iff₀ hfapos).mp hN
  obtain ⟨n,hn,hnpoly⟩ := hpoly (b*a*(N+1))
  have hnA : b*(N+1)≤n/a := (Nat.le_div_iff_mul_le ha).mpr (by nlinarith)
  have hnAp : n/a≠0 := by nlinarith
  let k := Nat.log b (n/a)
  let P := b^k
  have hP : P≤n/a := Nat.pow_log_le_self b hnAp
  have hP' : n/a<b*P := by
    have hh := Nat.lt_pow_of_log_lt (b := b) (x := k+1) (y := n/a) hb
      (show Nat.log b (n/a)<k+1 by omega)
    simpa only [pow_succ,Nat.mul_comm] using hh
  have hNP : N<P := by nlinarith
  have hNP' : (N:ℝ)<P := by exact_mod_cast hNP
  have hPA : P*a≤n := (Nat.le_div_iff_mul_le ha).mp hP
  have hnupper : n<(b*P)*a := (Nat.div_lt_iff_lt_mul ha).mp hP'
  have hlow : (P:ℝ)^d*((P:ℝ)*f a)≤f n := by
    have hh := (hgrow k).trans (hf hPA)
    have he : (P:ℝ)^d*((P:ℝ)*f a) = ((b:ℝ)^(d+1))^k*f a := by
      dsimp [P]
      push_cast
      rw [←mul_assoc,←pow_succ,←pow_mul,←pow_mul,Nat.mul_comm k (d+1)]
    rw [he]
    exact hh
  have hupper : f n≤(P:ℝ)^d*(C*((b*a:ℕ):ℝ)^d) := by
    have hnupper' : (n:ℝ)≤((b*P)*a:ℕ) := by exact_mod_cast hnupper.le
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hnupper' d) hC
    apply hnpoly.trans
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have hPpos : (0:ℝ)<(P:ℝ)^d := by
    apply pow_pos
    exact_mod_cast (show 0<P by dsimp [P]; positivity)
  have hsmall : C*((b*a:ℕ):ℝ)^d<(P:ℝ)*f a :=
    hNF.trans (mul_lt_mul_of_pos_right hNP' hfapos)
  exact (not_lt_of_ge (hlow.trans hupper)) (mul_lt_mul_of_pos_left hsmall hPpos)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SparseEnergyRatio
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CriticalPercolation.HarmonicAnalysis

lemma exists_small_relative_dissipation (E N : ℕ → ℝ)
    (hpos : ∀ n, 0<E n) (hm : Antitone E)
    (hdis : ∀ n, N n≤E n-E (n+1))
    (d : ℕ) (C : ℝ) (hC : 0≤C)
    (hg : ∀ R, ∃ n≥R, (E n)⁻¹≤C*(n:ℝ)^d)
    (ε : ℝ) (hε : 0<ε) : ∃ n, N n≤ε*E n := by
  by_contra! hbad
  have hmono : Monotone (fun n => (E n)⁻¹) := by
    intro i j hij
    exact (inv_le_inv₀ (hpos i) (hpos j)).mpr (hm hij)
  obtain ⟨R,hR⟩ := exists_nat_gt ((2:ℝ)^(d+1)/ε)
  obtain ⟨r,hr,hgood⟩ := sparse_real_doubling (fun n => (E n)⁻¹) hmono
    0 (fun n _ => inv_pos.mpr (hpos n)) C hC d 2 (by omega) hg R
  have hratio : E r≤(2:ℝ)^(d+1)*E (2*r) := by
    have hh : 1/E (2*r)≤(2:ℝ)^(d+1)/E r := by
      simpa only [Nat.cast_ofNat,one_div,div_eq_mul_inv,one_mul] using hgood
    have hh' := (div_le_div_iff₀ (hpos (2*r)) (hpos r)).mp hh
    simpa only [one_mul] using hh'
  have hεr : (2:ℝ)^(d+1)<(r:ℝ)*ε := by
    have hh : (R:ℝ) ≤ r := by exact_mod_cast (le_max_left R 0).trans hr
    have hh' := (div_lt_iff₀ hε).mp hR
    nlinarith
  have ht : ∀ i ≤ r, (i:ℝ)*ε*E (2*r)≤E r-E (r+i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have H := ih (by omega)
      have HD := (hbad (r+i)).le.trans (hdis (r+i))
      have HM := mul_le_mul_of_nonneg_left (hm (by omega : r+i≤2*r)) hε.le
      push_cast
      have he : r+(i+1)=r+i+1 := by omega
      rw [he]
      nlinarith
  have hh := ht r le_rfl
  rw [←two_mul] at hh
  have hh' := mul_lt_mul_of_pos_right hεr (hpos (2*r))
  nlinarith [hpos (2*r)]

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_FiniteHilbert
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
open HarmonicAnalysis

variable {X : Type*}

namespace FH
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → FH X) (x : X) :
    (∑ i∈s, f i) x=∑ i∈s, f i x := by
  simp only [Submodule.coe_sum,lp.coeFn_sum,Finset.sum_apply]

lemma eq_zero_of_not_mem (f : FH X) {x : X} (h : x∉f.support) : f x=0 :=
  not_not.mp ((f.mem_support x).not.mp h)

lemma delta_inner (x : X) (f : FH X) : inner ℝ (delta x) f=f x := by
  change inner ℝ (lp.single 2 x (1:ℝ)) f.val=f x
  rw [lp.inner_single_left]
  simp

lemma inner_eq_sum (f g : FH X) (F : Finset X) (hF : f.support⊆F) :
    inner ℝ f g=∑ x∈F, f x*g x := by
  change (∑' x, inner ℝ (f x) (g x))=_
  simp only [Real.inner_apply]
  apply tsum_eq_sum
  intro x hx
  rw [f.eq_zero_of_not_mem (fun h => hx (hF h)),zero_mul]
lemma norm_sq_eq_sum (f : FH X) (F : Finset X) (hF : f.support⊆F) :
    ‖f‖^2=∑ x∈F, (f x)^2 := by
  rw [←real_inner_self_eq_norm_sq,f.inner_eq_sum f F hF]
  simp only [pow_two]

lemma norm_coordinate_le (f : FH X) (x : X) : |f x|≤‖f‖ := by
  exact lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) f.val x

lemma delta_decomposition (f : FH X) :
    (∑ x∈f.support, f x • delta x)=f := by
  ext y
  rw [sum_apply]
  by_cases hy : y∈f.support
  · simp [delta_apply,hy]
  · simp [delta_apply,hy,f.eq_zero_of_not_mem hy]

lemma sum_sq_le_norm_sq (f : FH X) (F : Finset X) :
    (∑ x∈F, (f x)^2)≤‖f‖^2 := by
  rw [f.norm_sq_eq_sum (F∪f.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; positivity)

end FH
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphWalkOperator
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma averaging_coordinate (f : FH X) (x : X) :
    W.averaging f x=(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y := rfl

lemma averaging_delta (x : X) : W.averaging (FH.delta x)=
    (W.degree:ℝ)⁻¹ • ∑ y∈W.neighbors x, FH.delta y := by
  ext z
  simp only [W.averaging_coordinate,FH.smul_apply,FH.sum_apply,FH.delta_apply,
    Finset.sum_ite_eq,Finset.sum_ite_eq',W.mem_neighbors]
  congr 1
  congr 1
  exact propext (W.graph.adj_comm _ _)

lemma averaging_symmetric_delta (x : X) (f : FH X) :
    inner ℝ (W.averaging (FH.delta x)) f=inner ℝ (FH.delta x) (W.averaging f) := by
  rw [W.averaging_delta,(real_inner_smul_left (F:=FH X)),sum_inner,FH.delta_inner]
  simp only [FH.delta_inner,W.averaging_coordinate]

lemma averaging_symmetric (f g : FH X) : inner ℝ (W.averaging f) g=inner ℝ f (W.averaging g) := by
  calc
    _ = inner ℝ (W.averaging (∑ x∈f.support, f x • FH.delta x)) g := by rw [f.delta_decomposition]
    _ = ∑ x∈f.support, f x*inner ℝ (W.averaging (FH.delta x)) g := by
      simp only [map_sum,map_smul,sum_inner,(real_inner_smul_left (F:=FH X))]
    _ = inner ℝ (∑ x∈f.support, f x • FH.delta x) (W.averaging g) := by
      simp only [sum_inner,(real_inner_smul_left (F:=FH X)),W.averaging_symmetric_delta]
    _ = _ := by rw [f.delta_decomposition]

lemma sum_neighbor_sq_bound (F : Finset X) (f : FH X) :
    (∑ x∈F, ∑ y∈W.neighbors x, (f y)^2)≤(W.degree:ℝ)*‖f‖^2 := by
  let J := F.biUnion W.neighbors
  have hof : ∀ y∈J, (F.filter (fun x => y∈W.neighbors x)).card≤W.degree := by
    intro y hy
    calc
      _ ≤ (W.neighbors y).card := Finset.card_le_card (by
        intro x hx
        exact W.mem_neighbors.mpr (W.mem_neighbors.mp (Finset.mem_filter.mp hx).2).symm)
      _ = _ := W.neighbors_card y
  have hh := sum_le_sum_of_finite_overlap F W.neighbors J
    (fun x hx y hy => Finset.mem_biUnion.mpr ⟨x,hx,hy⟩) W.degree hof
    (fun y => (f y)^2) (fun y => sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_left (f.sum_sq_le_norm_sq J) (Nat.cast_nonneg _))

lemma averaging_norm_le (hD : 0<W.degree) (f : FH X) : ‖W.averaging f‖≤‖f‖ := by
  have hD' : (0:ℝ)<W.degree := by exact_mod_cast hD
  have hpoint (x : X) : (W.averaging f x)^2≤(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, (f y)^2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s:=W.neighbors x) (f:=fun y => f y)
    rw [W.neighbors_card] at hh
    rw [W.averaging_coordinate,mul_pow]
    have he : (W.degree:ℝ)⁻¹^2*(W.degree:ℝ)=(W.degree:ℝ)⁻¹ := by field_simp
    calc
      _ ≤ (W.degree:ℝ)⁻¹^2*((W.degree:ℝ)*∑ y∈W.neighbors x, (f y)^2) :=
        mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by rw [←mul_assoc,he]
  have hsum := Finset.sum_le_sum (fun x (_ : x∈(W.averaging f).support) => hpoint x)
  rw [←(W.averaging f).norm_sq_eq_sum _ (Finset.Subset.refl _),←Finset.mul_sum] at hsum
  have hbound := mul_le_mul_of_nonneg_left (W.sum_neighbor_sq_bound (W.averaging f).support f)
    (inv_nonneg.mpr hD'.le)
  rw [←mul_assoc,inv_mul_cancel₀ hD'.ne',one_mul] at hbound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsum.trans hbound)

lemma lazyWalk_apply (f : FH X) : W.lazyWalk f=(1/2:ℝ) • (f+W.averaging f) := rfl

lemma lazyWalk_coordinate (f : FH X) (x : X) : W.lazyWalk f x=
    (1/2:ℝ)*(f x+(W.degree:ℝ)⁻¹*∑ y∈W.neighbors x, f y) := rfl

lemma lazyWalk_symmetric (f g : FH X) :
    inner ℝ (W.lazyWalk f) g=inner ℝ f (W.lazyWalk g) := by
  simp only [W.lazyWalk_apply,(real_inner_smul_left (F:=FH X)),(real_inner_smul_right (F:=FH X)),
    inner_add_left,inner_add_right,W.averaging_symmetric]
lemma lazyWalk_norm_le (hD : 0<W.degree) (f : FH X) : ‖W.lazyWalk f‖≤‖f‖ := by
  rw [W.lazyWalk_apply,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have ht := norm_add_le f (W.averaging f)
  have ha := W.averaging_norm_le hD f
  linarith
lemma lazyWalk_positive (hD : 0<W.degree) (f : FH X) : 0 ≤ inner ℝ f (W.lazyWalk f) := by
  have hb := abs_real_inner_le_norm f (W.averaging f)
  have h := mul_le_mul_of_nonneg_left (W.averaging_norm_le hD f) (norm_nonneg f)
  have hl := (abs_le.mp (hb.trans h)).1
  simp only [W.lazyWalk_apply,(real_inner_smul_right (F:=FH X)),inner_add_right,real_inner_self_eq_norm_sq]
  nlinarith
lemma walkEnergy_nonneg (hD : 0<W.degree) (f : FH X) : 0≤W.walkEnergy f := by
  have hb := real_inner_le_norm f (W.lazyWalk f)
  have h := mul_le_mul_of_nonneg_left (W.lazyWalk_norm_le hD f) (norm_nonneg f)
  unfold walkEnergy
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  nlinarith
lemma walkEnergy_dissipation (hD : 0<W.degree) (f : FH X) :
    ‖f-W.lazyWalk f‖^2≤W.walkEnergy f-W.walkEnergy (W.lazyWalk f) := by
  have hp := W.lazyWalk_positive hD (f-W.lazyWalk f)
  rw [map_sub] at hp
  simp only [inner_sub_left,inner_sub_right] at hp
  rw [←W.lazyWalk_symmetric f (W.lazyWalk f)] at hp
  have hcomm : inner ℝ (W.lazyWalk f) f=inner ℝ f (W.lazyWalk f) := real_inner_comm _ _
  unfold walkEnergy
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  nlinarith [real_inner_self_eq_norm_sq (W.lazyWalk f)]

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphWalkProbability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma degree_pos [Infinite X] : 0<W.degree := by
  obtain ⟨x,hx⟩ := exists_ne W.root
  obtain ⟨p⟩ := W.connected W.root x
  cases p with
  | nil => exact (hx rfl).elim
  | @cons a y z h p => exact Finset.card_pos.mpr ⟨y,W.mem_neighbors.mpr h⟩

lemma averaging_mass (hD : 0<W.degree) (f : FH X) : FH.mass (W.averaging f)=FH.mass f := by
  have hc : (W.degree:ℝ)≠0 := by exact_mod_cast hD.ne'
  have hdelta (x : X) : FH.mass (W.averaging (FH.delta x))=1 := by
    rw [W.averaging_delta,map_smul,map_sum]
    simp only [FH.mass_delta,Finset.sum_const,nsmul_eq_mul,mul_one,smul_eq_mul,W.neighbors_card]
    exact inv_mul_cancel₀ hc
  rw [←f.delta_decomposition]
  simp only [map_sum,map_smul,hdelta,FH.mass_delta]
lemma lazyWalk_nonnegative (f : FH X) (hf : ∀ x, 0≤f x) : ∀ x, 0≤W.lazyWalk f x := by
  intro x
  rw [W.lazyWalk_coordinate]
  exact mul_nonneg (by norm_num) (add_nonneg (hf x)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun y hy => hf y))))
lemma lazyWalk_mass (hD : 0<W.degree) (f : FH X) : FH.mass (W.lazyWalk f)=FH.mass f := by
  rw [W.lazyWalk_apply,map_smul,map_add,W.averaging_mass hD]
  simp only [smul_eq_mul]; ring

lemma walkFeature_succ (n : ℕ) (x : X) : W.walkFeature (n+1) x=W.lazyWalk (W.walkFeature n x) := by
  simp only [walkFeature,pow_succ',Module.End.mul_apply]
lemma walkState_succ (n : ℕ) : W.walkState (n+1)=W.lazyWalk (W.walkState n) := W.walkFeature_succ n W.root
lemma walkState_nonnegative (n : ℕ) : ∀ x, 0≤W.walkState n x := by
  induction n with
  | zero => intro x; simp only [walkState,walkFeature_zero,FH.delta_apply]; split <;> norm_num
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_nonnegative _ ih
lemma walkState_mass (hD : 0<W.degree) (n : ℕ) : FH.mass (W.walkState n)=1 := by
  induction n with
  | zero => exact FH.mass_delta _
  | succ n ih => rw [W.walkState_succ,W.lazyWalk_mass hD,ih]
lemma walkState_root_pos (n : ℕ) : 0<W.walkState n W.root := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hs : 0≤(W.degree:ℝ)⁻¹*∑ y∈W.neighbors W.root, W.walkState n y := by
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun y hy => W.walkState_nonnegative n y))
    positivity
lemma walkState_support (n : ℕ) {x : X} (hx : x∉W.ball n) : W.walkState n x=0 := by
  induction n generalizing x with
  | zero =>
    have hne : x≠W.root := by intro h; apply hx; rw [h]; exact W.self_mem_around _ _
    simp [hne]
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate,ih (fun h => hx (W.ball_mono (by omega) h))]
    have hs : (∑ y∈W.neighbors x, W.walkState n y)=0 := by
      apply Finset.sum_eq_zero
      intro y hy
      apply ih
      intro hn
      apply hx
      apply W.mem_around_add hn
      exact W.mem_around.mpr ⟨SimpleGraph.Walk.cons (W.mem_neighbors.mp hy).symm .nil,by simp⟩
    rw [hs]; ring
lemma walkPower_symmetric (n : ℕ) (f g : FH X) :
    inner ℝ ((W.lazyWalk^n) f) g=inner ℝ f ((W.lazyWalk^n) g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    calc
      _ = inner ℝ ((W.lazyWalk^n) (W.lazyWalk f)) g := by rw [pow_succ,Module.End.mul_apply]
      _ = inner ℝ (W.lazyWalk f) ((W.lazyWalk^n) g) := ih _ _
      _ = inner ℝ f (W.lazyWalk ((W.lazyWalk^n) g)) := W.lazyWalk_symmetric _ _
      _ = _ := by rw [pow_succ',Module.End.mul_apply]
lemma walkState_double_at_root (n : ℕ) : W.walkState (2*n) W.root=‖W.walkState n‖^2 := by
  have hh := W.walkPower_symmetric n (FH.delta W.root) (W.walkState n)
  rw [FH.delta_inner] at hh
  have he : (W.lazyWalk^n) (W.walkState n)=W.walkState (2*n) := by
    simp only [walkState,walkFeature,←Module.End.mul_apply,←pow_add,two_mul]
  rw [he] at hh
  change inner ℝ (W.walkState n) (W.walkState n)=_ at hh
  rw [real_inner_self_eq_norm_sq] at hh
  exact hh.symm
lemma walkState_norm_sq (n : ℕ) : ‖W.walkState n‖^2=∑ x∈W.ball n, (W.walkState n x)^2 :=
  (W.walkState n).norm_sq_eq_sum _ (by
    intro x hx; by_contra hn; exact ((W.walkState n).mem_support x).mp hx (W.walkState_support n hn))
lemma walkState_norm_lower (hD : 0<W.degree) (n : ℕ) : 1≤((W.ball n).card:ℝ)*‖W.walkState n‖^2 := by
  have hmass : (∑ x∈W.ball n, W.walkState n x)=1 := by
    rw [←W.walkState_mass hD n]
    exact (tsum_eq_sum (f:=fun x => W.walkState n x) (s:=W.ball n)
      (fun x hx => W.walkState_support n hx)).symm
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (W.ball n) (fun _ => (1:ℝ)) (fun x => W.walkState n x)
  simpa only [one_mul,hmass,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,←W.walkState_norm_sq] using hc

lemma transport_averaging (g : W.Aut) (f : FH X) :
    FH.transport g.toEquiv (W.averaging f)=W.averaging (FH.transport g.toEquiv f) := by
  ext x
  simp only [FH.transport_apply,W.averaging_coordinate]
  congr 1
  change (∑ y∈W.neighbors (g.symm x), f y)=∑ y∈W.neighbors x, f (g.symm y)
  rw [←W.neighbors_image g.symm x,Finset.sum_image]
  exact fun a ha b hb h => g.symm.injective h
lemma transport_lazyWalk (g : W.Aut) (f : FH X) :
    FH.transport g.toEquiv (W.lazyWalk f)=W.lazyWalk (FH.transport g.toEquiv f) := by
  simp only [W.lazyWalk_apply,map_smul,map_add,W.transport_averaging]
lemma transport_walkFeature (g : W.Aut) (n : ℕ) (x : X) :
    FH.transport g.toEquiv (W.walkFeature n x)=W.walkFeature n (g x) := by
  induction n with
  | zero => exact FH.transport_delta _ _
  | succ n ih => rw [W.walkFeature_succ,W.transport_lazyWalk,ih,W.walkFeature_succ]
lemma walkFeature_norm (n : ℕ) (x : X) : ‖W.walkFeature n x‖=‖W.walkState n‖ := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.transport_walkFeature,LinearIsometryEquiv.norm_map]
lemma walkFeature_average (n : ℕ) (x : X) :
    (∑ y∈W.neighbors x, W.walkFeature n y)=(W.degree:ℝ) • W.averaging (W.walkFeature n x) := by
  have hc : W.averaging.comp W.lazyWalk=W.lazyWalk.comp W.averaging := by
    ext f y
    simp only [LinearMap.comp_apply,W.lazyWalk_apply,map_smul,map_add]
  have hcomm : ∀ n, W.averaging.comp (W.lazyWalk^n)=(W.lazyWalk^n).comp W.averaging := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change W.averaging*(W.lazyWalk^(n+1))=(W.lazyWalk^(n+1))*W.averaging
      rw [pow_succ',←mul_assoc,show W.averaging*W.lazyWalk=W.lazyWalk*W.averaging from hc,
        mul_assoc,show W.averaging*W.lazyWalk^n=W.lazyWalk^n*W.averaging from ih,←mul_assoc,←pow_succ']
  have hd (x : X) : (W.degree:ℝ) • W.averaging (FH.delta x)=∑ y∈W.neighbors x, FH.delta y := by
    by_cases hD : W.degree=0
    · have he : W.neighbors x=∅ := Finset.card_eq_zero.mp (by exact (W.neighbors_card x).trans hD)
      simp [hD,he]
    · rw [W.averaging_delta,smul_smul,mul_inv_cancel₀ (by exact_mod_cast hD),one_smul]
  calc
    _ = (W.lazyWalk^n) (∑ y∈W.neighbors x, FH.delta y) := (map_sum _ _ _).symm
    _ = (W.lazyWalk^n) ((W.degree:ℝ) • W.averaging (FH.delta x)) := by rw [hd]
    _ = _ := by rw [map_smul,←LinearMap.comp_apply,←hcomm,LinearMap.comp_apply]; rfl

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphWalkEnergy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma exists_ball_boundary [Infinite X] (r : ℕ) : ∃ x∈W.ball (r+1), x∉W.ball r := by
  by_contra! hbad
  have hb (n : ℕ) : W.ball n⊆W.ball r := by
    intro x hx
    obtain ⟨p,hp⟩ := W.mem_around.mp hx
    have hw : ∀ {a b : X}, (p : W.graph.Walk a b) → a∈W.ball r → b∈W.ball r := by
      intro a b p
      induction p with
      | nil => exact id
      | @cons a y b h p ih =>
        intro ha
        apply ih
        apply hbad
        exact W.mem_around_add ha (W.mem_around.mpr ⟨.cons h .nil,by simp⟩)
    exact hw p (W.self_mem_around _ _)
  have hf : (Set.univ:Set X).Finite := (W.ball r).finite_toSet.subset (by
    intro x _; obtain ⟨n,hn⟩ := W.exists_mem_ball x; exact hb n hn)
  exact Set.infinite_univ hf

lemma walkFeature_symmetric (n : ℕ) (x y : X) : W.walkFeature n x y=W.walkFeature n y x := by
  have h := W.walkPower_symmetric n (FH.delta x) (FH.delta y)
  rw [real_inner_comm,FH.delta_inner,FH.delta_inner] at h
  exact h

lemma walkEnergy_gradient (n : ℕ) :
    (∑ y∈W.neighbors W.root, ‖W.walkFeature n y-W.walkState n‖^2)=
      4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by
  simp only [norm_sub_sq_real,W.walkFeature_norm,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum,←sum_inner,W.walkFeature_average,
    real_inner_smul_left (F:=FH X)]
  unfold walkEnergy
  rw [inner_sub_right,W.lazyWalk_apply,real_inner_smul_right (F:=FH X),inner_add_right,
    real_inner_self_eq_norm_sq,W.averaging_symmetric]
  dsimp only [walkState,degree]
  ring

lemma feature_neighbor_bound (hD : 0<W.degree) (n : ℕ) {y : X} (hy : y∈W.neighbors W.root) :
    ‖W.walkFeature n y-W.walkState n‖≤Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  have hh := (Finset.single_le_sum (f:=fun y => ‖W.walkFeature n y-W.walkState n‖^2)
    (fun y hy => sq_nonneg _) hy).trans_eq (W.walkEnergy_gradient n)
  have he : 0≤4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg hD _)
  nlinarith [Real.sq_sqrt he,Real.sqrt_nonneg (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)),
    norm_nonneg (W.walkFeature n y-W.walkState n)]
lemma feature_edge_bound (hD : 0<W.degree) (n : ℕ) {x y : X} (h : W.graph.Adj x y) :
    ‖W.walkFeature n y-W.walkFeature n x‖≤Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  have he : W.walkFeature n y-W.walkFeature n (g W.root)=
      FH.transport g.toEquiv (W.walkFeature n (g.symm y)-W.walkState n) := by
    rw [map_sub,W.transport_walkFeature,W.transport_walkFeature,g.apply_symm_apply]
  rw [he,LinearIsometryEquiv.norm_map]
  apply W.feature_neighbor_bound hD
  exact W.mem_neighbors.mpr (by simpa using g.symm.map_adj_iff.mpr h)
lemma feature_walk_bound (hD : 0<W.degree) (n : ℕ) {x y : X} (p : W.graph.Walk x y) :
    ‖W.walkFeature n y-W.walkFeature n x‖≤(p.length:ℝ)*Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have he : W.walkFeature n z-W.walkFeature n x=
        (W.walkFeature n z-W.walkFeature n y)+(W.walkFeature n y-W.walkFeature n x) := by abel
    rw [he]
    have ht := norm_add_le (W.walkFeature n z-W.walkFeature n y) (W.walkFeature n y-W.walkFeature n x)
    have hb := W.feature_edge_bound hD n h
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith
lemma feature_ball_bound (hD : 0<W.degree) (n r : ℕ) {x : X} (hx : x∈W.ball r) :
    ‖W.walkFeature n x-W.walkState n‖≤(r:ℝ)*Real.sqrt (4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  obtain ⟨p,hp⟩ := W.mem_around.mp hx
  exact (W.feature_walk_bound hD n p).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (Real.sqrt_nonneg _))

lemma supported_energy_bound [Infinite X] (n : ℕ) :
    W.walkState n W.root^2≤(n+1:ℝ)^2*4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by
  obtain ⟨x,hx,hx'⟩ := W.exists_ball_boundary n
  have hp := (W.walkFeature n x-W.walkState n).norm_coordinate_le W.root
  have hb := W.feature_ball_bound W.degree_pos n (n+1) hx
  have hv : |(W.walkFeature n x-W.walkState n) W.root|=|W.walkState n W.root| := by
    rw [FH.sub_apply,W.walkFeature_symmetric,W.walkState_support n hx',zero_sub,abs_neg]
  rw [hv] at hp
  have ht := pow_le_pow_left₀ (abs_nonneg _) (hp.trans hb) 2
  have he : 0≤4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg W.degree_pos _)
  rw [mul_pow,Real.sq_sqrt he,sq_abs] at ht
  push_cast at ht
  nlinarith
lemma walkState_energy_pos [Infinite X] (n : ℕ) : 0<W.walkEnergy (W.walkState n) := by
  have hp := W.walkState_root_pos n
  have hb := W.supported_energy_bound n
  have hn := W.walkEnergy_nonneg W.degree_pos (W.walkState n)
  by_contra! h
  have he := le_antisymm h hn
  rw [he,mul_zero] at hb
  nlinarith
lemma walkState_energy_lower [Infinite X] (n : ℕ) :
    1≤((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.degree:ℝ)*W.walkEnergy (W.walkState (2*n)) := by
  have hn := W.walkState_norm_lower W.degree_pos n
  have hb := W.supported_energy_bound (2*n)
  rw [W.walkState_double_at_root] at hb
  have hsq : 1≤((W.ball n).card:ℝ)^2*(‖W.walkState n‖^2)^2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hn]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ((W.ball n).card:ℝ))
  push_cast at hh
  nlinarith
lemma walkState_energy_antitone (hD : 0<W.degree) : Antitone (fun n => W.walkEnergy (W.walkState n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := W.walkEnergy_dissipation hD (W.walkState n)
  rw [←W.walkState_succ] at h
  nlinarith [sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖]

lemma walk_energy_inverse_sparse [Infinite X] (d : ℕ)
    (hg : W.HasDegree d) :
    ∃ C : ℝ, 0≤C ∧ ∀ R, ∃ m≥R,
      (W.walkEnergy (W.walkState m))⁻¹≤C*(m:ℝ)^(2*d+2) := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨36*(W.degree:ℝ)*(C:ℝ)^2,by positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvol⟩ := hC (max R 1)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hnR : R≤n := (le_max_left R 1).trans hn
  refine ⟨2*n,by omega,?_⟩
  have hV : ((W.ball n).card:ℝ)≤(C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvol
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpoly : ((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.degree:ℝ)≤
      (36*(W.degree:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)^2*(3*(n:ℝ))^2*4*(W.degree:ℝ) := by
        gcongr
        linarith
      _ = (36*(W.degree:ℝ)*(C:ℝ)^2)*(n:ℝ)^(2*d+2) := by
        rw [pow_add,pow_mul]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  have hb := W.walkState_energy_lower n
  have hh := mul_le_mul_of_nonneg_right hpoly (W.walkState_energy_pos (2*n)).le
  have hf : 1≤((36*(W.degree:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2))*
      W.walkEnergy (W.walkState (2*n)) := hb.trans hh
  exact (inv_le_iff_one_le_mul₀ (W.walkState_energy_pos (2*n))).mpr hf

theorem exists_walk_small_relative_residual [Infinite X] (d : ℕ)
    (hg : W.HasDegree d) (ε : ℝ) (hε : 0<ε) :
    ∃ n, 0<W.walkEnergy (W.walkState n) ∧
      ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2≤ε*W.walkEnergy (W.walkState n) := by
  obtain ⟨C,hC,hpoly⟩ := W.walk_energy_inverse_sparse d hg
  obtain ⟨n,hn⟩ := exists_small_relative_dissipation
    (fun n => W.walkEnergy (W.walkState n))
    (fun n => ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2)
    W.walkState_energy_pos (W.walkState_energy_antitone W.degree_pos)
    (fun n => by simpa only [W.walkState_succ] using W.walkEnergy_dissipation W.degree_pos (W.walkState n))
    (2*d+2) C hC hpoly ε hε
  exact ⟨n,W.walkState_energy_pos n,hn⟩

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphProjectedFunctions
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma exists_large_neighbor_gradient (hD : 0<W.degree) (n : ℕ) :
    ∃ t∈W.neighbors W.root, 4*W.walkEnergy (W.walkState n)≤‖W.walkFeature n t-W.walkState n‖^2 := by
  by_contra! h
  have hh := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hD) (fun t ht => h t ht)
  rw [W.walkEnergy_gradient] at hh
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  nlinarith
lemma projectedFunction_root (n : ℕ) (t : X) : W.projectedFunction n t W.root=0 := by
  simp [projectedFunction,walkState]
lemma projectedFunction_edge_bound [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) {x y : X} (hxy : W.graph.Adj x y) :
    |W.projectedFunction n t y-W.projectedFunction n t x|≤1 := by
  let q := 4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<q := by dsimp [q]; positivity
  have he : (W.walkFeature n y-W.walkState n)-(W.walkFeature n x-W.walkState n)=
      W.walkFeature n y-W.walkFeature n x := by abel
  unfold projectedFunction
  rw [←sub_div,←inner_sub_left,he,abs_div,abs_of_pos hq]
  apply (div_le_one hq).mpr
  calc
    _ ≤ ‖W.walkFeature n y-W.walkFeature n x‖*‖W.walkFeature n t-W.walkState n‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt q*Real.sqrt q := mul_le_mul (W.feature_edge_bound W.degree_pos n hxy)
      (W.feature_neighbor_bound W.degree_pos n ht) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q := Real.mul_self_sqrt hq.le
lemma projectedFunction_length_bound [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) (x : X) : |W.projectedFunction n t x|≤(W.length x:ℝ) := by
  let q := 4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<q := by dsimp [q]; positivity
  unfold projectedFunction
  rw [abs_div,abs_of_pos hq]
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ ‖W.walkFeature n x-W.walkState n‖*‖W.walkFeature n t-W.walkState n‖ := abs_real_inner_le_norm _ _
    _ ≤ ((W.length x:ℝ)*Real.sqrt q)*Real.sqrt q :=
      mul_le_mul (W.feature_ball_bound W.degree_pos n _ (W.mem_ball_length x))
        (W.feature_neighbor_bound W.degree_pos n ht) (norm_nonneg _) (by positivity)
    _ = (W.length x:ℝ)*q := by rw [mul_assoc,Real.mul_self_sqrt hq.le]
lemma projectedFunction_neighbor_lower [Infinite X] (n : ℕ) (t : X)
    (ht : 4*W.walkEnergy (W.walkState n)≤‖W.walkFeature n t-W.walkState n‖^2) :
    (W.degree:ℝ)⁻¹≤W.projectedFunction n t t := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hq : 0<4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) := by positivity
  unfold projectedFunction
  rw [real_inner_self_eq_norm_sq]
  apply (le_div_iff₀ hq).mpr
  have he : (W.degree:ℝ)⁻¹*(4*(W.degree:ℝ)*W.walkEnergy (W.walkState n))=4*W.walkEnergy (W.walkState n) := by field_simp
  rw [he]; exact ht
lemma sum_feature_displacement (n : ℕ) (x : X) :
    (∑ y∈W.neighbors x, (W.walkFeature n x-W.walkFeature n y))=
      (2*(W.degree:ℝ)) • (W.walkFeature n x-W.lazyWalk (W.walkFeature n x)) := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ,
    W.neighbors_card,W.walkFeature_average,W.lazyWalk_apply]
  module
lemma projectedFunction_residual (n : ℕ) (t x : X) :
    (∑ y∈W.neighbors x, (W.projectedFunction n t x-W.projectedFunction n t y))=
      (2*(W.degree:ℝ))*inner ℝ (W.walkFeature n x-W.lazyWalk (W.walkFeature n x))
        (W.walkFeature n t-W.walkState n)/(4*(W.degree:ℝ)*W.walkEnergy (W.walkState n)) := by
  simp only [projectedFunction,←sub_div,←Finset.sum_div,←inner_sub_left,←sum_inner]
  have he : (∑ y∈W.neighbors x, (W.walkFeature n x-W.walkState n-(W.walkFeature n y-W.walkState n)))=
      ∑ y∈W.neighbors x, (W.walkFeature n x-W.walkFeature n y) := by
    apply Finset.sum_congr rfl; intros; abel
  rw [he,W.sum_feature_displacement,real_inner_smul_left (F:=FH X)]
lemma feature_residual_norm (n : ℕ) (x : X) :
    ‖W.walkFeature n x-W.lazyWalk (W.walkFeature n x)‖=‖W.walkState n-W.lazyWalk (W.walkState n)‖ := by
  obtain ⟨g,rfl⟩ := W.transitive W.root x
  rw [←W.transport_walkFeature,←W.transport_lazyWalk,←map_sub,LinearIsometryEquiv.norm_map]
lemma projectedFunction_residual_sq [Infinite X] (n : ℕ) (t : X)
    (ht : t∈W.neighbors W.root) (x : X) :
    (∑ y∈W.neighbors x, (W.projectedFunction n t x-W.projectedFunction n t y))^2≤
      (W.degree:ℝ)*‖W.walkState n-W.lazyWalk (W.walkState n)‖^2/W.walkEnergy (W.walkState n) := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hf := W.walkState_energy_pos n
  have hgrad := (Finset.single_le_sum (f:=fun y => ‖W.walkFeature n y-W.walkState n‖^2)
    (fun y hy => sq_nonneg _) ht).trans_eq (W.walkEnergy_gradient n)
  have hi := abs_real_inner_le_norm (W.walkFeature n x-W.lazyWalk (W.walkFeature n x))
    (W.walkFeature n t-W.walkState n)
  rw [W.feature_residual_norm] at hi
  have hisq := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs,mul_pow] at hisq
  have hb := mul_le_mul_of_nonneg_left hgrad (sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖)
  rw [W.projectedFunction_residual,div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos (show 0<4*(W.degree:ℝ)*W.walkEnergy (W.walkState n) by positivity)) hf).mpr
  have hm := mul_le_mul_of_nonneg_left (hisq.trans hb)
    (show 0≤4*(W.degree:ℝ)^2*W.walkEnergy (W.walkState n) by positivity)
  nlinarith only [hm]
end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphHarmonicCompactness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter
open scoped Classical Pointwise BigOperators Topology

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {A : Type*} (W : Geometry A)

include W in
lemma countable_vertices : Countable A := by
  apply Set.countable_univ_iff.mp
  have hc : (⋃ n:ℕ, (W.ball n:Set A)).Countable :=
    Set.countable_iUnion (fun n => (W.ball n).finite_toSet.countable)
  apply hc.mono
  intro a _
  obtain ⟨n,hn⟩ := W.exists_mem_ball a
  exact Set.mem_iUnion.mpr ⟨n,hn⟩

lemma exists_projected_approximation [Infinite A] (d : ℕ)
    (hg : W.HasDegree d) (δ : ℝ) (hδ : 0<δ) :
    ∃ u : A → ℝ, u W.root=0 ∧ (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x y, W.graph.Adj x y → |u y-u x|≤1) ∧
      (W.degree:ℝ)⁻¹^2≤∑ s∈W.neighbors W.root, (u s)^2 ∧
      ∀ x, |∑ s∈W.neighbors x, (u x-u s)|≤δ := by
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  obtain ⟨n,hE,hres⟩ := W.exists_walk_small_relative_residual d hg
    (δ^2/(W.degree:ℝ)) (div_pos (sq_pos_of_pos hδ) hc)
  let f := W.walkState n
  obtain ⟨t,ht,hlarge⟩ := W.exists_large_neighbor_gradient W.degree_pos n
  let u := W.projectedFunction n t
  have hlow := W.projectedFunction_neighbor_lower n t hlarge
  refine ⟨u,W.projectedFunction_root n t,W.projectedFunction_length_bound n t ht,
    fun x y h => W.projectedFunction_edge_bound n t ht h,?_,?_⟩
  · have hs : (W.degree:ℝ)⁻¹^2≤(u t)^2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hlow 2
    exact hs.trans (Finset.single_le_sum (fun s hs => sq_nonneg (u s)) ht)
  · intro x
    have h := W.projectedFunction_residual_sq n t ht x
    have hb : (W.degree:ℝ)*‖f-W.lazyWalk f‖^2/W.walkEnergy f≤δ^2 := by
      apply (div_le_iff₀ hE).mpr
      have hh := mul_le_mul_of_nonneg_left hres hc.le
      have he : (W.degree:ℝ)*(δ^2/(W.degree:ℝ)*W.walkEnergy f)=δ^2*W.walkEnergy f := by
        field_simp
      rw [he] at hh
      exact hh
    have hh : (∑ s∈W.neighbors x, (u x-u s))^2≤δ^2 := h.trans hb
    nlinarith [sq_abs (∑ s∈W.neighbors x, (u x-u s)),abs_nonneg (∑ s∈W.neighbors x, (u x-u s))]

theorem exists_nonconstant_lipschitz_harmonic [Infinite A] (d : ℕ)
    (hg : W.HasDegree d) :
    ∃ u : A → ℝ, W.IsHarmonic u ∧ u W.root=0 ∧
      (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x y, W.graph.Adj x y → |u y-u x|≤1) ∧
      ∃ s∈W.neighbors W.root, u s≠0 := by
  let _ : Countable A := W.countable_vertices
  have hδ (n:ℕ) : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  choose v hv1 hvbound hvedge hvgrad hvres using
    (fun n : ℕ => W.exists_projected_approximation d hg (1/((n:ℝ)+1)) (hδ n))
  let K : Set (A → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-(W.length x:ℝ)) (W.length x:ℝ))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hvK (n:ℕ) : v n∈K := by
    intro x hx
    exact abs_le.mp (hvbound n x)
  obtain ⟨u,huK,φ,hφ,hlim⟩ := hK.tendsto_subseq hvK
  have hxlim (x:A) : Tendsto (fun n => v (φ n) x) atTop (𝓝 (u x)) :=
    (continuous_apply x).continuousAt.tendsto.comp hlim
  have hu1 : u W.root=0 := by
    have hh : Tendsto (fun n => v (φ n) W.root) atTop (𝓝 0) := by
      simpa only [hv1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hxlim W.root) hh
  have hbound (x:A) : |u x|≤(W.length x:ℝ) := abs_le.mpr (huK x (Set.mem_univ x))
  have hedge (x y:A) (h:W.graph.Adj x y) : |u y-u x|≤1 :=
    le_of_tendsto ((hxlim y).sub (hxlim x)).abs (Filter.Eventually.of_forall (fun n => hvedge (φ n) x y h))
  have hgrad : (W.degree:ℝ)⁻¹^2≤∑ s∈W.neighbors W.root, (u s)^2 := by
    have hl := tendsto_finsetSum (W.neighbors W.root) (fun s hs => (hxlim s).pow 2)
    exact ge_of_tendsto hl (Filter.Eventually.of_forall (fun n => hvgrad (φ n)))
  have hharm : W.IsHarmonic u := by
    intro x
    have hl := tendsto_finsetSum (W.neighbors x) (fun s hs => (hxlim x).sub (hxlim s))
    have hz : Tendsto (fun n : ℕ => 1/((φ n:ℝ)+1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    have hnonneg : (0:ℝ)≤ |∑ s∈W.neighbors x, (u x-u s)| := abs_nonneg _
    have hle : |∑ s∈W.neighbors x, (u x-u s)|≤0 :=
      le_of_tendsto_of_tendsto hl.abs hz (Filter.Eventually.of_forall (fun n => hvres (φ n) x))
    exact abs_eq_zero.mp (le_antisymm hle hnonneg)
  refine ⟨u,hharm,hu1,hbound,hedge,?_⟩
  by_contra! hn
  have hz : (∑ s∈W.neighbors W.root, (u s)^2)=0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [hn s hs]
    norm_num
  rw [hz] at hgrad
  have hc : (0:ℝ)<W.degree := by exact_mod_cast W.degree_pos
  have hp := sq_pos_of_pos (inv_pos.mpr hc)
  linarith

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_GraphHarmonicLinear
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma harmonic_constant_of_attained_max {u : X → ℝ} (hu : W.IsHarmonic u)
    (a : X) (hmax : ∀ x, u x≤u a) : ∀ x, u x=u a := by
  have hstep {x y : X} (hx : u x=u a) (hxy : W.graph.Adj x y) : u y=u a := by
    have hn (z : X) (hz : z∈W.neighbors x) : 0≤u x-u z := by rw [hx]; exact sub_nonneg.mpr (hmax z)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp (hu x) y (W.mem_neighbors.mpr hxy)
    linarith
  have hw : ∀ {x y : X}, W.graph.Walk x y → u x=u a → u y=u a := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z h p ih => exact fun hx => ih (hstep hx h)
  intro x
  obtain ⟨p⟩ := W.connected a x
  exact hw p rfl
lemma harmonic_constant_of_finite_range {u : X → ℝ} (hu : W.IsHarmonic u)
    (hf : (Set.range u).Finite) : ∀ x, u x=u W.root := by
  let : Nonempty X := ⟨W.root⟩
  obtain ⟨m,⟨a,rfl⟩,hm⟩ := Set.exists_max_image (Set.range u) id hf (Set.range_nonempty u)
  have he := W.harmonic_constant_of_attained_max hu a (fun x => hm (u x) ⟨x,rfl⟩)
  exact fun x => (he x).trans (he W.root).symm

variable {G : Type*} [Group G] (τ : G →* W.Aut)
lemma finite_range_of_finite_harmonic_image (k : ℕ)
    (htrans : ∀ x, ∃ a : G, τ a W.root=x)
    (hf : (Set.range ((W.harmonicRepresentation k).comp τ)).Finite) (u : W.polynomialHarmonicSpace k) :
    (Set.range (u:X → ℝ)).Finite := by
  apply (hf.image (fun e => (e u:X → ℝ) W.root)).subset
  rintro y ⟨x,rfl⟩
  obtain ⟨a,ha⟩ := htrans x
  refine ⟨(W.harmonicRepresentation k).comp τ a⁻¹,⟨a⁻¹,rfl⟩,?_⟩
  change (u:X → ℝ) ((τ a⁻¹).symm W.root)=(u:X → ℝ) x
  rw [map_inv]
  change (u:X → ℝ) (τ a W.root)=(u:X → ℝ) x
  rw [ha]
lemma infinite_harmonic_linear_image [Infinite X] (d : ℕ) (hg : W.HasDegree d)
    (htrans : ∀ x, ∃ a : G, τ a W.root=x) :
    (Set.range ((W.harmonicRepresentation 1).comp τ)).Infinite := by
  obtain ⟨u,hu,hu1,hbound,hedge,s,hs,hne⟩ := W.exists_nonconstant_lipschitz_harmonic d hg
  have hupol : W.HasPolynomialGrowth 1 u := by
    apply (W.polynomial_growth_iff_length 1 u).mpr
    refine ⟨1,by norm_num,?_⟩
    intro x
    simpa only [pow_one,one_mul] using (hbound x).trans (by linarith : (W.length x:ℝ)≤(W.length x:ℝ)+1)
  let v : W.polynomialHarmonicSpace 1 := ⟨u,hu,hupol⟩
  intro hf
  have hconst := W.harmonic_constant_of_finite_range hu
    (W.finite_range_of_finite_harmonic_image τ 1 htrans hf v)
  exact hne ((hconst s).trans hu1)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Nilpotent_CharacteristicNilpotentCore
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma HasPolynomialDegree.of_surjective {d : ℕ} (hg : HasPolynomialDegree A d)
    (f : A →* B) (hf : Surjective f) : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,C,hC⟩ := (hasPolynomialDegree_iff d).mp hg
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image f,Finset.mem_image.mpr ⟨1,h1,map_one f⟩,?_,?_,C,?_⟩
  · rw [←Finset.image_inv,hs]
  · rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · intro R
    obtain ⟨n,hn,hb⟩ := hC R
    refine ⟨n,hn,le_trans ?_ hb⟩
    rw [←Finset.image_pow]
    exact Finset.card_image_le

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_InvariantBlockSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Module Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

lemma commute_of_identity_on_subspace_quotient (W : Submodule K V) (e f : V ≃ₗ[K] V)
    (heW : ∀ w∈W, e w=w) (hfW : ∀ w∈W, f w=w)
    (heQ : ∀ v, e v-v∈W) (hfQ : ∀ v, f v-v∈W) : e*f=f*e := by
  ext v
  have he := heW (f v-v) (hfQ v)
  have hf := hfW (e v-v) (heQ v)
  rw [map_sub] at he hf
  change e (f v)=f (e v)
  have h1 : e (f v)=f v-v+e v := (sub_eq_iff_eq_add).mp he
  have h2 : f (e v)=e v-v+f v := (sub_eq_iff_eq_add).mp hf
  rw [h1,h2]
  abel

lemma solvable_of_subspace_quotient (ρ : G →* (V ≃ₗ[K] V)) (hρ : Injective ρ)
    (W : Submodule K V) (hW : ∀ g, W.map (ρ g).toLinearMap=W)
    [Group.IsSolvable (subspaceRepresentation ρ W hW).range]
    [Group.IsSolvable (quotientRepresentation ρ W hW).range] : Group.IsSolvable G := by
  let σ := subspaceRepresentation ρ W hW
  let τ := quotientRepresentation ρ W hW
  let ψ := σ.rangeRestrict.prod τ.rangeRestrict
  have hker : Group.IsSolvable ψ.ker := by
    apply Group.isSolvable_of_comm
    intro x y
    apply Subtype.ext
    apply hρ
    change ρ (x.val*y.val)=ρ (y.val*x.val)
    rw [map_mul,map_mul]
    have hs (g : ψ.ker) : σ g.val=1 := by
      have he := congrArg (fun z : σ.range × τ.range => (z.1 : W ≃ₗ[K] W)) g.property
      exact he
    have ht (g : ψ.ker) : τ g.val=1 := by
      have he := congrArg (fun z : σ.range × τ.range => (z.2 : (V ⧸ W) ≃ₗ[K] (V ⧸ W))) g.property
      exact he
    have hsub (g : ψ.ker) (w : V) (hw : w∈W) : ρ g.val w=w :=
      congrArg (fun e : W ≃ₗ[K] W => (e ⟨w,hw⟩ : V)) (hs g)
    have hquot (g : ψ.ker) (v : V) : ρ g.val v-v∈W := by
      apply (Submodule.Quotient.eq W).mp
      exact congrArg (fun e : (V ⧸ W) ≃ₗ[K] (V ⧸ W) => e (Submodule.Quotient.mk v)) (ht g)
    exact commute_of_identity_on_subspace_quotient W (ρ x.val) (ρ y.val)
      (hsub x) (hsub y) (hquot x) (hquot y)
  let := hker
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by simp)

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_BurnsideDensity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma toModuleEnd_surjective_of_simple {K A V : Type*} [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower K A V] [IsSimpleModule A V] [FiniteDimensional K V] :
    Surjective (Module.toModuleEnd K (S:=A) V) := by
  let E := Module.End A V
  have he : Surjective (algebraMap K E) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K).2
  let : Module.Finite E V := Module.Finite.of_restrictScalars_finite K E V
  intro T
  let T' : Module.End E V := {
    toFun := T
    map_add' := T.map_add
    map_smul' := by
      intro e x
      obtain ⟨c,rfl⟩ := he e
      change T (c • x)=c • T x
      exact T.map_smul c x }
  obtain ⟨a,ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R:=A) (M:=V) T'
  refine ⟨a,?_⟩
  ext x
  exact congrArg (fun f : Module.End E V => f x) ha

lemma subalgebra_eq_top_of_simple {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Subalgebra K (Module.End K V))
    [IsSimpleModule A V] : A=⊤ := by
  apply top_unique
  intro T _
  obtain ⟨a,ha⟩ := toModuleEnd_surjective_of_simple (K:=K) (A:=A) (V:=V) T
  have he : (a : Module.End K V)=T := by
    ext v
    exact congrArg (fun f : Module.End K V => f v) ha
  exact he ▸ a.property

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_InvariantSubspaceDensity
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Nontrivial V] [Group G]

lemma invariant_subspace_of_not_fullSpan (ρ : G →* (V ≃ₗ[K] V)) (hρ : ¬FullSpan ρ) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧ ∀ g, W.map (ρ g).toLinearMap=W := by
  let σ : G →* End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  let A := Algebra.adjoin K ((MonoidHom.mrange σ) : Set (End K V))
  have hAspan : A.toSubmodule=Submodule.span K (Set.range (fun g => (ρ g).toLinearMap)) := by
    rw [Algebra.adjoin_eq_span,Submonoid.closure_eq]
    rfl
  have hA : A≠⊤ := by
    intro he
    apply hρ
    change Submodule.span K (Set.range (fun g => (ρ g).toLinearMap))=⊤
    rw [←hAspan,he]
    rfl
  have hns : ¬IsSimpleModule A V := by
    intro h
    exact hA (subalgebra_eq_top_of_simple A)
  have he : ∃ P : Submodule A V, P≠⊥ ∧ P≠⊤ := by
    by_contra hn
    push Not at hn
    have : IsSimpleOrder (Submodule A V) := IsSimpleOrder.of_forall_eq_top hn
    exact hns ⟨⟩
  obtain ⟨P,hP0,hP1⟩ := he
  let W := P.restrictScalars K
  have hρmem (g : G) : (ρ g).toLinearMap∈A :=
    Algebra.subset_adjoin (show σ g∈(MonoidHom.mrange σ) from ⟨g,rfl⟩)
  have hstable (g : G) {v : V} (hv : v∈W) : ρ g v∈W :=
    P.smul_mem ⟨(ρ g).toLinearMap,hρmem g⟩ hv
  refine ⟨W,?_,?_,?_⟩
  · intro hw
    apply hP0
    apply Submodule.restrictScalars_injective K A V
    simpa only [Submodule.restrictScalars_bot] using hw
  · intro hw
    apply hP1
    apply Submodule.restrictScalars_injective K A V
    simpa only [Submodule.restrictScalars_top] using hw
  · intro g
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hstable g hx
    · intro hv
      refine ⟨ρ g⁻¹ v,hstable g⁻¹ hv,?_⟩
      simp only [map_inv,LinearEquiv.coe_coe,LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_FgMatrixRing
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma exists_finiteType_matrix_ring [Group.FG G] (ρ : G →* GL n R) :
    ∃ D : Subalgebra ℤ R, Algebra.FiniteType ℤ D ∧ ∀ g i j, ρ g i j∈D := by
  obtain ⟨S,hS,hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let T := hSf.toFinset ∪ hSf.toFinset⁻¹
  let E := T.biUnion (fun g => Finset.univ.biUnion (fun i => Finset.univ.image (fun j => ρ g i j)))
  let D := Algebra.adjoin ℤ (E : Set R)
  have hD : Algebra.FiniteType ℤ D := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset E)
  have hgen (g : G) (hg : g∈T) (i j : n) : ρ g i j∈D := by
    apply Algebra.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩⟩
  refine ⟨D,hD,?_⟩
  intro g
  have hg : g∈Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction'' with
  | mem a ha => exact hgen a (Finset.mem_union_left _ (hSf.mem_toFinset.mpr ha))
  | inv_mem a ha =>
    apply hgen a⁻¹
    apply Finset.mem_union_right
    simpa using hSf.mem_toFinset.mpr ha
  | one =>
    intro i j
    rw [map_one]
    by_cases h : i=j <;> simp [h,D.zero_mem,D.one_mem]
  | mul a b ha hb iha ihb =>
    intro i j
    rw [map_mul]
    change (∑ l, ρ a i l*ρ b l j)∈D
    exact D.sum_mem (fun l _ => D.mul_mem (iha i l) (ihb l j))

variable (ρ : G →* GL n R) (D : Subalgebra ℤ R) (hD : ∀ g i j, ρ g i j∈D)

lemma liftMatrixGroup_injective (hρ : Injective ρ) : Injective (liftMatrixGroup ρ D hD) := by
  intro x y he
  apply hρ
  apply Units.ext
  ext i j
  exact congrArg (fun M : GL n D => ((M i j : D) : R)) he

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_AlgebraicVirtualSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma finiteIndex_comap_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f) (P : Subgroup B) [P.FiniteIndex] :
    (P.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap,f.range_eq_top_of_surjective hf,Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero

lemma solvable_range_of_mem {A B : Type*} [Group A] [Group B]
    (f : A →* B) (P : Subgroup B) [Group.IsSolvable P] (hp : ∀ a, f a∈P) :
    Group.IsSolvable f.range := by
  have hh : f.range≤P := by rintro _ ⟨a,rfl⟩; exact hp a
  exact Group.isSolvable_of_isSolvable_injective (f:=Subgroup.inclusion hh)
    (Subgroup.inclusion_injective hh)

lemma solvable_restricted_range {A B : Type*} [Group A] [Group B]
    (f : A →* B) (P : Subgroup f.range) [Group.IsSolvable P]
    (J : Subgroup A) (hJ : J≤P.comap f.rangeRestrict) :
    Group.IsSolvable (f.comp J.subtype).range := by
  let Q := P.map f.range.subtype
  let e := P.equivMapOfInjective f.range.subtype Subtype.val_injective
  let : Group.IsSolvable Q := Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective
  apply solvable_range_of_mem (f.comp J.subtype) Q
  intro j
  exact ⟨f.rangeRestrict j.val,hJ j.property,rfl⟩

lemma virtually_solvable_linear_of_rank (K : Type) [Field K] [CharZero K]
    [Countable K] [IsAlgClosed K] (r : ℕ) :
    ∀ (V G : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Group G] [DecidableEq G], finrank K V=r →
      ∀ (ρ : G →* (V ≃ₗ[K] V)), Injective ρ →
      ∀ d, SparseGrowth.HasPolynomialDegree G d →
      ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro V G _ _ _ _ _ hr ρ hρ d hg
    rcases subsingleton_or_nontrivial V with hv | hv
    · let := hv
      have hc : ∀ g h : G, g*h=h*g := by
        intro g h
        apply hρ
        exact Subsingleton.elim _ _
      let : Group.IsSolvable G := Group.isSolvable_of_comm hc
      exact ⟨⊤,inferInstance,inferInstance⟩
    let := hv
    by_cases hd : StrongFullSpan ρ
    · obtain ⟨H,hHi,hH⟩ := hd.virtually_comm_range_bs ρ hg
      let : Group.IsSolvable (ρ.comp H.subtype).range := Group.isSolvable_of_comm hH
      have hinj : Injective (ρ.comp H.subtype).rangeRestrict := by
        intro x y he
        apply Subtype.ext
        apply hρ
        exact congrArg Subtype.val he
      exact ⟨H,hHi,Group.isSolvable_of_isSolvable_injective hinj⟩
    obtain ⟨H,hHi,hH⟩ : ∃ H : Subgroup G, H.FiniteIndex ∧ ¬FullSpan (ρ.comp H.subtype) := by
      simp only [StrongFullSpan,not_forall] at hd
      obtain ⟨H,hHi,hH⟩ := hd
      exact ⟨H,hHi,hH⟩
    let := hHi
    let ρH := ρ.comp H.subtype
    have hgH := hg.finiteIndex_subgroup H
    obtain ⟨W,hW0,hW1,hW⟩ := invariant_subspace_of_not_fullSpan ρH hH
    let σ := subspaceRepresentation ρH W hW
    let τ := quotientRepresentation ρH W hW
    have hWrank : finrank K W < r := hr ▸ Submodule.finrank_lt hW1
    have hQrank : finrank K (V ⧸ W) < r := by
      have he := W.finrank_quotient_add_finrank
      have hp : 0 < finrank K W := by
        let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
        exact Module.finrank_pos (R:=K) (M:=W)
      omega
    have hgσ := hgH.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
    have hgτ := hgH.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
    obtain ⟨P,hPi,hPs⟩ := ih _ hWrank W σ.range rfl σ.range.subtype Subtype.val_injective d hgσ
    obtain ⟨Q,hQi,hQs⟩ := ih _ hQrank (V ⧸ W) τ.range rfl τ.range.subtype Subtype.val_injective d hgτ
    let := hPi
    let := hQi
    let := hPs
    let := hQs
    let J := P.comap σ.rangeRestrict ⊓ Q.comap τ.rangeRestrict
    let : (P.comap σ.rangeRestrict).FiniteIndex :=
      finiteIndex_comap_surjective σ.rangeRestrict σ.rangeRestrict_surjective P
    let : (Q.comap τ.rangeRestrict).FiniteIndex :=
      finiteIndex_comap_surjective τ.rangeRestrict τ.rangeRestrict_surjective Q
    let : J.FiniteIndex := inferInstance
    have hWJ (j : J) : W.map (ρH j.val).toLinearMap=W := hW j.val
    have hsJ : subspaceRepresentation (ρH.comp J.subtype) W hWJ=σ.comp J.subtype := by
      ext j w; rfl
    have htJ : quotientRepresentation (ρH.comp J.subtype) W hWJ=τ.comp J.subtype := by
      ext j v
      induction v using Submodule.Quotient.induction_on
      rfl
    let : Group.IsSolvable (subspaceRepresentation (ρH.comp J.subtype) W hWJ).range :=
      hsJ.symm ▸ solvable_restricted_range σ P J inf_le_left
    let : Group.IsSolvable (quotientRepresentation (ρH.comp J.subtype) W hWJ).range :=
      htJ.symm ▸ solvable_restricted_range τ Q J inf_le_right
    let : Group.IsSolvable J := solvable_of_subspace_quotient (ρH.comp J.subtype)
      ((hρ.comp Subtype.val_injective).comp Subtype.val_injective) W hWJ
    let L := J.map H.subtype
    let e := J.equivMapOfInjective H.subtype Subtype.val_injective
    have hLi : L.FiniteIndex := by
      constructor
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero (inferInstance : J.FiniteIndex).index_ne_zero hHi.index_ne_zero
    exact ⟨L,hLi,Group.isSolvable_of_surjective (f:=e.toMonoidHom) e.surjective⟩

lemma virtually_solvable_linear (K V G : Type) [Field K] [CharZero K]
    [Countable K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group G] [DecidableEq G] (ρ : G →* (V ≃ₗ[K] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H :=
  virtually_solvable_linear_of_rank K (finrank K V) V G rfl ρ hρ degree hg

end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_LinearGroups_RealVirtualSolvability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical Cardinal

namespace CriticalPercolation.LinearGrowth

lemma countable_finiteType_int (D : Type) [CommRing D] [Algebra ℤ D]
    [Algebra.FiniteType ℤ D] : Countable D := by
  obtain ⟨n,f,hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial).mp
    (inferInstance : Algebra.FiniteType ℤ D)
  let : Countable (MvPolynomial n ℤ) := by
    apply Function.Injective.countable (f := AddMonoidAlgebra.coeff)
    intro x y h
    cases x; cases y; cases h; rfl
  exact Function.Surjective.countable hf

lemma countable_fraction (D : Type) [CommRing D] [Countable D] : Countable (FractionRing D) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_fractionRing]
  exact Cardinal.mk_le_aleph0

lemma countable_algebraicClosure (F : Type) [Field F] [Countable F] :
    Countable (AlgebraicClosure F) := by
  have h := Algebraic.countable F (AlgebraicClosure F)
  have he : {x : AlgebraicClosure F | IsAlgebraic F x}=Set.univ :=
    Set.eq_univ_of_forall (fun _ => Algebra.IsAlgebraic.isAlgebraic _)
  rw [he] at h
  exact Set.countable_univ_iff.mp h

lemma matrixRepresentation_injective {K G n : Type} [Field K] [Group G]
    [Fintype n] [DecidableEq n] (ρ : G →* GL n K) (hρ : Injective ρ) :
    Injective (matrixRepresentation ρ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).injective.comp
    (Matrix.GeneralLinearGroup.toLin.injective.comp hρ)

lemma virtually_solvable_real_matrix {G n : Type} [Group G] [DecidableEq G]
    [Fintype n] [DecidableEq n] (ρ : G →* GL n ℝ) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let := hg.fg
  obtain ⟨D,hD,hm⟩ := exists_finiteType_matrix_ring ρ
  let := hD
  let : Countable D := countable_finiteType_int D
  let F := FractionRing D
  let K := AlgebraicClosure F
  let : Countable F := countable_fraction D
  let : Countable K := countable_algebraicClosure F
  let f : D →+* K := (algebraMap F K).comp (algebraMap D F)
  have hf : Injective f := (algebraMap F K).injective.comp (IsFractionRing.injective D F)
  let σ := liftMatrixGroup ρ D hm
  let τ := (Matrix.GeneralLinearGroup.map f).comp σ
  have hσ : Injective σ := liftMatrixGroup_injective ρ D hm hρ
  have hτ : Injective τ := by
    intro x y h
    apply hσ
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply hf
    exact congrArg (fun M : GL n K => M i j) h
  exact virtually_solvable_linear K (n → K) G (matrixRepresentation τ)
    (matrixRepresentation_injective τ hτ) hg

end CriticalPercolation.LinearGrowth

namespace CriticalPercolation.LinearGrowth
lemma virtually_solvable_real_linear_general {G V : Type*} [Group G] [DecidableEq G]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : G →* (V ≃ₗ[ℝ] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let τ := (linearMatrixEquiv (K:=ℝ) (V:=V)).toMonoidHom.comp ρ
  have hτ : Injective τ := linearMatrixEquiv.injective.comp hρ
  have hgτ := hg.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  obtain ⟨P,hPi,hPs⟩ := virtually_solvable_real_matrix τ.range.subtype Subtype.val_injective hgτ
  let := hPi
  let := hPs
  let H := P.comap τ.rangeRestrict
  have hHi : H.FiniteIndex := finiteIndex_comap_surjective τ.rangeRestrict τ.rangeRestrict_surjective P
  let ψ : H →* P := (τ.rangeRestrict.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Injective ψ := by
    intro x y he
    apply Subtype.ext
    apply hτ
    exact congrArg (fun z : P => (z.val : GL (Fin (finrank ℝ V)) ℝ)) he
  exact ⟨H,hHi,Group.isSolvable_of_isSolvable_injective hψ⟩
end CriticalPercolation.LinearGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Harmonic_WeakGromovHarmonic
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth

lemma infinite_finiteIndex_subgroup {A : Type*} [Group A] [Infinite A]
    (H : Subgroup A) [H.FiniteIndex] : Infinite H := by
  rcases finite_or_infinite H with hf | hi
  · let := hf
    let : Finite A := H.finite_iff_finite_and_finiteIndex.mpr ⟨hf,inferInstance⟩
    exact False.elim (_root_.not_finite A)
  · exact hi

lemma indicability_of_finiteIndex {A : Type*} [Group A] (P : Subgroup A) [P.FiniteIndex]
    (hp : ∃ Q : Subgroup P, Q.FiniteIndex ∧ ∃ f : Q →* Multiplicative ℤ, Surjective f) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  obtain ⟨Q,hQi,f,hf⟩ := hp
  let H := Q.map P.subtype
  let e := Q.equivMapOfInjective P.subtype Subtype.val_injective
  have hHi : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hQi.index_ne_zero (inferInstance : P.FiniteIndex).index_ne_zero
  exact ⟨H,hHi,f.comp e.symm.toMonoidHom,hf.comp e.symm.surjective⟩

lemma indicability_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Surjective f)
    (hb : ∃ P : Subgroup B, P.FiniteIndex ∧ ∃ q : P →* Multiplicative ℤ, Surjective q) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ, Surjective q := by
  obtain ⟨P,hPi,q,hq⟩ := hb
  let := hPi
  let H := P.comap f
  let ψ : H →* P := (f.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Surjective ψ := by
    intro p
    obtain ⟨a,ha⟩ := hf p.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change f a∈P
    rw [ha]
    exact p.property
  exact ⟨H,LinearGrowth.finiteIndex_comap_surjective f hf P,q.comp ψ,hq.comp hψ⟩

lemma HasPolynomialDegree.linear_virtually_indicable {A : Type*} [Group A] [DecidableEq A]
    {d : ℕ} (hg : HasPolynomialDegree A d) [Infinite A] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ f : H →* Multiplicative ℤ, Surjective f := by
  let : DecidableEq A := Classical.decEq A
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (hasPolynomialDegree_iff d).mp hg
  let W : HarmonicAnalysis.WordGeometry A := ⟨S,h1,hi,hgen⟩
  obtain ⟨V,hV,hM,hfd,ρ,hρ⟩ := W.exists_infinite_finiteDimensional_linear_image_bs d hgS
  let := hV
  let := hM
  let := hfd
  have hgR := hg.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  let : Infinite ρ.range := hρ.to_subtype
  obtain ⟨P,hPi,hPs⟩ := LinearGrowth.virtually_solvable_real_linear_general
    ρ.range.subtype Subtype.val_injective hgR
  let := hPi
  let := hPs
  let : Infinite P := infinite_finiteIndex_subgroup P
  apply indicability_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  apply indicability_of_finiteIndex P
  exact (hgR.finiteIndex_subgroup P).virtually_indicable

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetIndicability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma finite_image_to_integer_ker (K : Subgroup A) (f : A →* Multiplicative ℤ)
    (hf : (f '' (K:Set A)).Finite) : K≤f.ker := by
  let J := K.map f
  let : Finite J := hf.to_subtype
  intro k hk
  let j : J := ⟨f k,Subgroup.mem_map.mpr ⟨k,hk,rfl⟩⟩
  obtain ⟨n,hn,he⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite j)
  have hm : (f k)^n=1 := congrArg Subtype.val he
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hm⟩).eq_one'

lemma indicability_pullback_killing (K : Subgroup A) (f : A →* B) (hf : Surjective f)
    (hK : (f '' (K:Set A)).Finite)
    (hb : ∃ P : Subgroup B, P.FiniteIndex ∧ ∃ q : P →* Multiplicative ℤ, Surjective q) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  obtain ⟨P,hPi,q,hq⟩ := hb
  let := hPi
  let H := P.comap f
  let ψ : H →* P := (f.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Surjective ψ := by
    intro p
    obtain ⟨a,ha⟩ := hf p.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change f a∈P
    rw [ha]
    exact p.property
  refine ⟨H,LinearGrowth.finiteIndex_comap_surjective f hf P,q.comp ψ,hq.comp hψ,?_⟩
  apply finite_image_to_integer_ker
  change ((fun h => q (ψ h)) '' (K.subgroupOf H:Set H)).Finite
  rw [←Set.image_image q ψ]
  apply Set.Finite.image
  apply Set.Finite.of_finite_image (f:=P.subtype)
  · apply hK.subset
    rintro _ ⟨p,⟨h,hh,rfl⟩,rfl⟩
    exact ⟨h.val,hh,rfl⟩
  · exact P.subtype_injective.injOn

lemma Presentation.virtually_indicable (P : Presentation A) (d : ℕ)
    (hg : HasDegree P.K P.S d) [Infinite P.X] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ P.K.subgroupOf H≤q.ker := by
  let W := P.geometry (hg.1 1)
  let ρ := (W.harmonicRepresentation 1).comp P.actionHom
  have hWg : W.HasDegree d := P.geometry_hasDegree d hg
  have htrans : ∀ x : P.X, ∃ a : A, P.actionHom a W.root=x := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨a,by change P.projection (a*1)=P.projection a; rw [mul_one]⟩
  have hInf : (Set.range ρ).Infinite := W.infinite_harmonic_linear_image P.actionHom d hWg htrans
  have hKρ : (ρ '' (P.K:Set A)).Finite := by
    apply (W.finite_stabilizer_harmonic_image_bs d 1 hWg).subset
    rintro _ ⟨k,hk,rfl⟩
    have hstab : P.actionHom k∈W.Stab := by
      change P.projection (k*1)=P.projection 1
      apply QuotientGroup.eq.mpr
      simpa using P.K.inv_mem hk
    exact ⟨⟨P.actionHom k,hstab⟩,rfl⟩
  let f := ρ.rangeRestrict
  have hKf : (f '' (P.K:Set A)).Finite := by
    apply Set.Finite.of_finite_image (f:=ρ.range.subtype)
    · simpa only [Set.image_image] using (show ((fun x => ρ.range.subtype (f x)) '' (P.K:Set A)).Finite from hKρ)
    · exact ρ.range.subtype_injective.injOn
  have hgR := hg.image_polynomial P.one_mem P.inv_eq P.generates f ρ.rangeRestrict_surjective hKf
  let : Infinite ρ.range := hInf.to_subtype
  exact indicability_pullback_killing P.K f ρ.rangeRestrict_surjective hKf hgR.linear_virtually_indicable

lemma virtually_indicable_bs_oai {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hg : HasDegree K S d) [Infinite (A ⧸ K)] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  obtain ⟨P,hPK,hPb,hSP⟩ := normalized_generators K S h1 hi hgen hK
  have hgP : HasDegree P.K P.S d := hPK.symm ▸ hg.bounded_generators h1 hPb
  let : Infinite P.X := by change Infinite (A ⧸ P.K); rw [hPK]; infer_instance
  exact hPK ▸ P.virtually_indicable d hgP

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs_oai.{u_1} := @OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs_oai.{u_1}
