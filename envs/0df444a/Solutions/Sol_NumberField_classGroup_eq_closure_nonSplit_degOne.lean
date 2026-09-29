-- Prove2me | solution 1 for NumberField.classGroup_eq_closure_nonSplit_degOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f448ee61-add0-5df7-b853-fd81b31377cf

import Definitions.Def_NumberField_IsSplitPrime
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_NumberField_tsum_split_degOne_le
import Mathlib.NumberTheory.NumberField.ClassNumber
import Theorems.Thm_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne

set_option autoImplicit false

section SplicePart0

open UniqueFactorizationMonoid

open scoped ENNReal Classical

section Core

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

private def MemSupp (T : Set (Ideal R)) (I : Ideal R) : Prop :=
  I ≠ 0 ∧ ∀ P ∈ normalizedFactors I, P ∈ T

omit [IsDomain R] in
private lemma memSupp_univ {I : Ideal R} (hI : I ≠ 0) : MemSupp Set.univ I :=
  ⟨hI, fun _ _ => Set.mem_univ _⟩

omit [IsDomain R] in
private lemma memSupp_mono {T T' : Set (Ideal R)} (h : T ⊆ T') {I : Ideal R}
    (hI : MemSupp T I) : MemSupp T' I :=
  ⟨hI.1, fun P hP => h (hI.2 P hP)⟩

private lemma memSupp_mul {T : Set (Ideal R)} {I J : Ideal R}
    (hI : MemSupp T I) (hJ : MemSupp T J) : MemSupp T (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, fun P hP => ?_⟩
  rw [normalizedFactors_mul hI.1 hJ.1, Multiset.mem_add] at hP
  exact hP.elim (hI.2 P) (hJ.2 P)

private lemma memSupp_one (T : Set (Ideal R)) : MemSupp T (1 : Ideal R) :=
  ⟨one_ne_zero, fun P hP => by
    rw [normalizedFactors_one] at hP
    exact absurd hP (by simp)⟩

omit [IsDomain R] in

private lemma normalizedFactors_filter_prod (A : Ideal R)
    (p : Ideal R → Prop) [DecidablePred p] :
    normalizedFactors (((normalizedFactors A).filter p).prod)
      = (normalizedFactors A).filter p := by
  refine normalizedFactors_prod_of_prime fun q hq => ?_
  exact prime_of_normalized_factor q ((Multiset.mem_filter.mp hq).1)

private lemma filter_prod_ne_zero (A : Ideal R)
    (p : Ideal R → Prop) [DecidablePred p] :
    ((normalizedFactors A).filter p).prod ≠ 0 :=
  Multiset.prod_ne_zero_of_prime _ fun q hq =>
    prime_of_normalized_factor q ((Multiset.mem_filter.mp hq).1)

private noncomputable def suppSplit (T S : Set (Ideal R)) (hd : Disjoint T S) :
    {I : Ideal R // MemSupp T I} × {J : Ideal R // MemSupp S J} ≃
      {A : Ideal R // MemSupp (T ∪ S) A} where
  toFun p := ⟨p.1.1 * p.2.1,
    memSupp_mul (memSupp_mono Set.subset_union_left p.1.2)
      (memSupp_mono Set.subset_union_right p.2.2)⟩
  invFun A := by
    refine ⟨⟨((normalizedFactors A.1).filter (· ∈ T)).prod, filter_prod_ne_zero A.1 _,
        fun P hP => ?_⟩,
      ⟨((normalizedFactors A.1).filter (· ∉ T)).prod, filter_prod_ne_zero A.1 _,
        fun P hP => ?_⟩⟩
    · rw [normalizedFactors_filter_prod A.1] at hP
      exact (Multiset.mem_filter.mp hP).2
    · rw [normalizedFactors_filter_prod A.1] at hP
      obtain ⟨hPA, hPT⟩ := Multiset.mem_filter.mp hP
      exact (A.2.2 P hPA).resolve_left hPT
  left_inv := by
    rintro ⟨⟨I, hI0, hIT⟩, ⟨J, hJ0, hJS⟩⟩
    have hnf : normalizedFactors (I * J) = normalizedFactors I + normalizedFactors J :=
      normalizedFactors_mul hI0 hJ0
    have hfilT : (normalizedFactors (I * J)).filter (· ∈ T) = normalizedFactors I := by
      rw [hnf, Multiset.filter_add, Multiset.filter_eq_self.mpr hIT,
        Multiset.filter_eq_nil.mpr fun P hP => Set.disjoint_right.mp hd (hJS P hP),
        add_zero]
    have hfilT' : (normalizedFactors (I * J)).filter (· ∉ T) = normalizedFactors J := by
      rw [hnf, Multiset.filter_add,
        Multiset.filter_eq_nil.mpr fun P hP => not_not_intro (hIT P hP),
        Multiset.filter_eq_self.mpr fun P hP => Set.disjoint_right.mp hd (hJS P hP),
        zero_add]
    have hIeq : (normalizedFactors I).prod = I := by
      rw [prod_normalizedFactors_eq hI0, normalize_eq]
    have hJeq : (normalizedFactors J).prod = J := by
      rw [prod_normalizedFactors_eq hJ0, normalize_eq]
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨by rw [hfilT, hIeq], by rw [hfilT', hJeq]⟩
  right_inv := by
    rintro ⟨A, hA0, hAsupp⟩
    simp only [Subtype.mk.injEq]
    rw [← Multiset.prod_add, Multiset.filter_add_not,
      prod_normalizedFactors_eq hA0, normalize_eq]

private lemma tsum_memSupp_mul_ennreal {T S : Set (Ideal R)} (hd : Disjoint T S)
    (f : Ideal R → ℝ≥0∞)
    (hf : ∀ I J : Ideal R, MemSupp T I → MemSupp S J → f (I * J) = f I * f J) :
    (∑' A : {A : Ideal R // MemSupp (T ∪ S) A}, f A.1) =
      (∑' I : {I : Ideal R // MemSupp T I}, f I.1) *
        (∑' J : {J : Ideal R // MemSupp S J}, f J.1) := by
  rw [← Equiv.tsum_eq (suppSplit T S hd) (fun A => f A.1)]
  have h1 : ∀ p : {I : Ideal R // MemSupp T I} × {J : Ideal R // MemSupp S J},
      f ((suppSplit T S hd) p).1 = f p.1.1 * f p.2.1 := by
    rintro ⟨I, J⟩; exact hf I.1 J.1 I.2 J.2
  calc (∑' p : {I : Ideal R // MemSupp T I} × {J : Ideal R // MemSupp S J},
          f ((suppSplit T S hd) p).1)
      = ∑' p : {I : Ideal R // MemSupp T I} × {J : Ideal R // MemSupp S J},
          f p.1.1 * f p.2.1 := tsum_congr h1
    _ = ∑' I : {I : Ideal R // MemSupp T I}, ∑' J : {J : Ideal R // MemSupp S J},
          f I.1 * f J.1 := ENNReal.tsum_prod'
    _ = ∑' I : {I : Ideal R // MemSupp T I}, f I.1 *
          ∑' J : {J : Ideal R // MemSupp S J}, f J.1 := by
          exact tsum_congr fun I => ENNReal.tsum_mul_left
    _ = _ := ENNReal.tsum_mul_right

private lemma tsum_memSupp_mul_complex {T S : Set (Ideal R)} (hd : Disjoint T S)
    (F : Ideal R → ℂ)
    (hF : ∀ I J : Ideal R, MemSupp T I → MemSupp S J → F (I * J) = F I * F J)
    (hT : Summable fun I : {I : Ideal R // MemSupp T I} => ‖F I.1‖)
    (hS : Summable fun J : {J : Ideal R // MemSupp S J} => ‖F J.1‖) :
    (∑' A : {A : Ideal R // MemSupp (T ∪ S) A}, F A.1) =
      (∑' I : {I : Ideal R // MemSupp T I}, F I.1) *
        (∑' J : {J : Ideal R // MemSupp S J}, F J.1) := by
  rw [← Equiv.tsum_eq (suppSplit T S hd) (fun A => F A.1),
    tsum_mul_tsum_of_summable_norm hT hS]
  refine tsum_congr ?_
  rintro ⟨I, J⟩
  exact hF I.1 J.1 I.2 J.2

end Core

section PrimePowers

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

private lemma memSupp_pow_singleton {v : Ideal R} (hv : Prime v) (k : ℕ) :
    MemSupp ({v} : Set (Ideal R)) (v ^ k) := by
  refine ⟨pow_ne_zero k hv.ne_zero, fun P hP => ?_⟩
  rw [normalizedFactors_pow, normalizedFactors_irreducible hv.irreducible,
    normalize_eq, Multiset.nsmul_singleton] at hP
  have : P = v := Multiset.eq_of_mem_replicate hP
  exact this ▸ Set.mem_singleton v

set_option maxHeartbeats 1600000 in

private noncomputable def powEquiv {v : Ideal R} (hv : Prime v) :
    ℕ ≃ {I : Ideal R // MemSupp {v} I} where
  toFun k := ⟨v ^ k, memSupp_pow_singleton hv k⟩
  invFun I := (normalizedFactors I.1).card
  left_inv k := by
    simp only [normalizedFactors_pow, normalizedFactors_irreducible hv.irreducible,
      normalize_eq, Multiset.nsmul_singleton, Multiset.card_replicate]
  right_inv := by
    rintro ⟨I, hI0, hIv⟩
    simp only [Subtype.mk.injEq]
    have hrep : normalizedFactors I = Multiset.replicate (normalizedFactors I).card v :=
      Multiset.eq_replicate_card.mpr fun P hP => Set.mem_singleton_iff.mp (hIv P hP)
    calc v ^ (normalizedFactors I).card
        = (Multiset.replicate (normalizedFactors I).card v).prod :=
          (Multiset.prod_replicate _ v).symm
      _ = (normalizedFactors I).prod := by rw [← hrep]
      _ = I := by rw [prod_normalizedFactors_eq hI0, normalize_eq]

private lemma tsum_memSupp_singleton_ennreal {v : Ideal R} (hv : Prime v)
    (f : Ideal R → ℝ≥0∞) :
    (∑' I : {I : Ideal R // MemSupp {v} I}, f I.1) = ∑' k : ℕ, f (v ^ k) :=
  ((powEquiv hv).tsum_eq fun I => f I.1).symm

private lemma tsum_memSupp_singleton_complex {v : Ideal R} (hv : Prime v)
    (F : Ideal R → ℂ) :
    (∑' I : {I : Ideal R // MemSupp {v} I}, F I.1) = ∑' k : ℕ, F (v ^ k) :=
  ((powEquiv hv).tsum_eq fun I => F I.1).symm

private def suppIncl {T T' : Set (Ideal R)} (h : T ⊆ T') :
    {I : Ideal R // MemSupp T I} → {I : Ideal R // MemSupp T' I} :=
  fun I => ⟨I.1, memSupp_mono h I.2⟩

omit [IsDomain R] in
private lemma suppIncl_injective {T T' : Set (Ideal R)} (h : T ⊆ T') :
    Function.Injective (suppIncl (R := R) h) := by
  rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ
  simpa [suppIncl] using hIJ

omit [IsDomain R] in
private lemma summable_norm_restrict {T T' : Set (Ideal R)} (h : T ⊆ T')
    {F : Ideal R → ℂ}
    (hsum : Summable fun I : {I : Ideal R // MemSupp T' I} => ‖F I.1‖) :
    Summable fun I : {I : Ideal R // MemSupp T I} => ‖F I.1‖ := by
  have := hsum.comp_injective (suppIncl_injective h)
  simpa only [Function.comp_def, suppIncl] using this

private lemma tsum_memSupp_peel_complex (W : Ideal R → ℂ)
    (hmul : ∀ I J : Ideal R, I ≠ 0 → J ≠ 0 → W (I * J) = W I * W J)
    (F : Finset (Ideal R)) :
    ∀ S : Set (Ideal R), ↑F ⊆ S → (∀ v ∈ S, Prime v) →
    (Summable fun I : {I : Ideal R // MemSupp S I} => ‖W I.1‖) →
    (∑' A : {A : Ideal R // MemSupp S A}, W A.1) =
      (∏ v ∈ F, ∑' k : ℕ, W (v ^ k)) *
        (∑' B : {B : Ideal R // MemSupp (S \ ↑F) B}, W B.1) := by
  classical
  induction F using Finset.induction with
  | empty =>
    intro S _ _ _
    have h : S \ (↑(∅ : Finset (Ideal R)) : Set (Ideal R)) = S := by simp
    rw [Finset.prod_empty, one_mul, h]
  | insert v F' hvF' ih =>
    intro S hFS hSprime hsum
    have hvS : v ∈ S := hFS (Finset.mem_insert_self v F')
    have hvprime : Prime v := hSprime v hvS
    have hsplit : ({v} : Set (Ideal R)) ∪ (S \ {v}) = S := by
      rw [Set.singleton_union, Set.insert_diff_singleton, Set.insert_eq_self.mpr hvS]
    have hdisj : Disjoint ({v} : Set (Ideal R)) (S \ {v}) :=
      Set.disjoint_sdiff_right.mono_left le_rfl
    have hmul' : ∀ I J : Ideal R, MemSupp {v} I → MemSupp (S \ {v}) J →
        W (I * J) = W I * W J := fun I J hI hJ => hmul I J hI.1 hJ.1
    have hS1 : Summable fun I : {I : Ideal R // MemSupp {v} I} => ‖W I.1‖ :=
      summable_norm_restrict (by simpa using Set.singleton_subset_iff.mpr hvS) hsum
    have hS2 : Summable fun I : {I : Ideal R // MemSupp (S \ {v}) I} => ‖W I.1‖ :=
      summable_norm_restrict Set.diff_subset hsum
    have hstep := tsum_memSupp_mul_complex (R := R) hdisj W hmul' hS1 hS2
    rw [hsplit] at hstep
    have hF'sub : ↑F' ⊆ S \ {v} := by
      intro w hw
      refine ⟨hFS (Finset.mem_insert_of_mem hw), ?_⟩
      rintro rfl
      exact hvF' hw
    have hrec := ih (S \ {v}) hF'sub (fun w hw => hSprime w hw.1) hS2
    rw [hstep, hrec, tsum_memSupp_singleton_complex hvprime,
      Finset.prod_insert hvF']
    have hsets : (S \ {v}) \ ↑F' = S \ ↑(insert v F') := by
      rw [Set.diff_diff, Finset.coe_insert, Set.insert_eq]
    rw [hsets]; ring

omit [IsDomain R] in

private lemma tsum_memSupp_mono {T T' : Set (Ideal R)} (h : T ⊆ T')
    (f : Ideal R → ℝ≥0∞) :
    (∑' I : {I : Ideal R // MemSupp T I}, f I.1) ≤
      ∑' I : {I : Ideal R // MemSupp T' I}, f I.1 :=
  ENNReal.tsum_comp_le_tsum_of_injective (suppIncl_injective h) (fun I => f I.1)

omit [IsDomain R] in

private lemma tsum_memSupp_eq_iSup (S : Set (Ideal R)) (f : Ideal R → ℝ≥0∞) :
    (∑' I : {I : Ideal R // MemSupp S I}, f I.1) =
      ⨆ F : {F : Finset (Ideal R) // ↑F ⊆ S},
        ∑' I : {I : Ideal R // MemSupp ↑F.1 I}, f I.1 := by
  classical
  refine le_antisymm ?_ (iSup_le fun F => tsum_memSupp_mono F.2 f)
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun u => ?_

  set Fu : Finset (Ideal R) := u.biUnion fun I => (normalizedFactors I.1).toFinset with hFu
  have hFuS : ↑Fu ⊆ S := by
    intro P hP
    simp only [hFu, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Multiset.mem_toFinset] at hP
    obtain ⟨I, _, hPI⟩ := hP
    exact I.2.2 P hPI
  refine le_trans ?_ (le_iSup _ (⟨Fu, hFuS⟩ : {F : Finset (Ideal R) // ↑F ⊆ S}))

  have hmem : ∀ I ∈ u, MemSupp (↑Fu : Set (Ideal R)) I.1 := by
    intro I hI
    refine ⟨I.2.1, fun P hP => ?_⟩
    simp only [hFu, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Multiset.mem_toFinset]
    exact ⟨I, hI, hP⟩
  calc ∑ I ∈ u, f I.1
      = ∑ J ∈ u.attach.image
          (fun I => (⟨I.1.1, hmem I.1 I.2⟩ : {J : Ideal R // MemSupp ↑Fu J})), f J.1 := by
        rw [Finset.sum_image ?_]
        · rw [← Finset.sum_attach u fun I => f I.1]
        · rintro ⟨⟨I, hI⟩, hIu⟩ - ⟨⟨J, hJ⟩, hJu⟩ - hIJ
          simpa [Subtype.ext_iff] using hIJ
    _ ≤ _ := ENNReal.sum_le_tsum _

private lemma tsum_memSupp_peel_ennreal (f : Ideal R → ℝ≥0∞)
    (hmul : ∀ I J : Ideal R, I ≠ 0 → J ≠ 0 → f (I * J) = f I * f J)
    (F : Finset (Ideal R)) :
    ∀ S : Set (Ideal R), ↑F ⊆ S → (∀ v ∈ S, Prime v) →
    (∑' A : {A : Ideal R // MemSupp S A}, f A.1) =
      (∏ v ∈ F, ∑' k : ℕ, f (v ^ k)) *
        (∑' B : {B : Ideal R // MemSupp (S \ ↑F) B}, f B.1) := by
  classical
  induction F using Finset.induction with
  | empty =>
    intro S _ _
    have h : S \ (↑(∅ : Finset (Ideal R)) : Set (Ideal R)) = S := by simp
    rw [Finset.prod_empty, one_mul, h]
  | insert v F' hvF' ih =>
    intro S hFS hSprime
    have hvS : v ∈ S := hFS (Finset.mem_insert_self v F')
    have hvprime : Prime v := hSprime v hvS
    have hsplit : ({v} : Set (Ideal R)) ∪ (S \ {v}) = S := by
      rw [Set.singleton_union, Set.insert_diff_singleton, Set.insert_eq_self.mpr hvS]
    have hdisj : Disjoint ({v} : Set (Ideal R)) (S \ {v}) :=
      Set.disjoint_sdiff_right.mono_left le_rfl
    have hmul' : ∀ I J : Ideal R, MemSupp {v} I → MemSupp (S \ {v}) J →
        f (I * J) = f I * f J := fun I J hI hJ => hmul I J hI.1 hJ.1
    have hstep := tsum_memSupp_mul_ennreal (R := R) hdisj f hmul'
    rw [hsplit] at hstep
    have hF'sub : ↑F' ⊆ S \ {v} := by
      intro w hw
      refine ⟨hFS (Finset.mem_insert_of_mem hw), ?_⟩
      rintro rfl
      exact hvF' hw
    have hrec := ih (S \ {v}) hF'sub (fun w hw => hSprime w hw.1)
    rw [hstep, hrec, tsum_memSupp_singleton_ennreal hvprime,
      Finset.prod_insert hvF']
    have hsets : (S \ {v}) \ ↑F' = S \ ↑(insert v F') := by
      rw [Set.diff_diff, Finset.coe_insert, Set.insert_eq]
    rw [hsets]; ring

omit [IsDomain R] in

private lemma eq_one_of_memSupp_empty {I : Ideal R} (h : MemSupp (∅ : Set (Ideal R)) I) :
    I = 1 := by
  have hnf : normalizedFactors I = 0 :=
    Multiset.eq_zero_of_forall_notMem fun P hP => (h.2 P hP).elim
  have := prod_normalizedFactors_eq h.1
  rw [hnf, Multiset.prod_zero, normalize_eq] at this
  exact this.symm

private scoped instance uniqueMemSuppEmpty : Unique {I : Ideal R // MemSupp (∅ : Set (Ideal R)) I} where
  default := ⟨1, memSupp_one ∅⟩
  uniq I := Subtype.ext (eq_one_of_memSupp_empty I.2)

private lemma tsum_memSupp_empty_ennreal (f : Ideal R → ℝ≥0∞) :
    (∑' A : {A : Ideal R // MemSupp (∅ : Set (Ideal R)) A}, f A.1) = f 1 := by
  rw [tsum_eq_single (default : {I : Ideal R // MemSupp (∅ : Set (Ideal R)) I})
    (fun b hb => absurd (Subsingleton.elim b default) hb)]
  rfl

private lemma tsum_memSupp_empty_complex (F : Ideal R → ℂ) :
    (∑' A : {A : Ideal R // MemSupp (∅ : Set (Ideal R)) A}, F A.1) = F 1 := by
  rw [tsum_eq_single (default : {I : Ideal R // MemSupp (∅ : Set (Ideal R)) I})
    (fun b hb => absurd (Subsingleton.elim b default) hb)]
  rfl

end PrimePowers

end SplicePart0

section SplicePart1

p2m_open "Filter Ideal NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField NumberField.InfinitePlace NumberField.Units Topology nonZeroDivisors Finset Asymptotics"

section Vocab

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

private def nsgT1 : Set (Ideal (𝓞 K)) :=
  {P | P.IsMaximal ∧ (Ideal.absNorm P).Prime ∧ ¬ IsSplitPrime K M P}

private def nsgPrimes : Set (Ideal (𝓞 K)) := {P | P.IsMaximal}

private def nsgS1 : Set (Ideal (𝓞 K)) := nsgPrimes K \ nsgT1 K M

private noncomputable def nsgWr (s : ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  ((Ideal.absNorm I : ℝ) ^ s)⁻¹

private noncomputable def nsgTail (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' v : S, nsgWr K s v.1

private noncomputable def nsgChi (χ : ClassGroup (𝓞 K) →* ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if h : I ≠ 0 then χ (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero h⟩) else 0

private noncomputable def nsgWc (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℝ) (I : Ideal (𝓞 K)) :
    ℂ :=
  nsgChi K χ I * ((nsgWr K s I : ℝ) : ℂ)

end Vocab

section Analytic

variable (M : Type*) [Field M] [NumberField M]

private noncomputable def nsgRTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (Nat.card {I : Ideal (𝓞 M) // absNorm I = n} : ℝ) / (n : ℝ) ^ s

private lemma nsgRTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ nsgRTerm M s n := by
  unfold nsgRTerm
  split_ifs
  · exact le_rfl
  · positivity

private lemma nsg_term_eq (s : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 M) // absNorm I = n} : ℂ)) (s : ℂ) n =
      (nsgRTerm M s n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero, nsgRTerm]
  · rw [LSeries.term_of_ne_zero hn, nsgRTerm, if_neg hn, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

private lemma nsg_tendsto_sum_card_div :
    Tendsto (fun n : ℕ ↦
      (∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 M) // absNorm I = k} : ℝ)) / (n : ℝ)) atTop
        (𝓝 (dedekindZeta_residue M)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ M).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 M) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private lemma nsg_LSeriesSummable {s : ℝ} (hs : 1 < s) :
    LSeriesSummable
      (fun n ↦ ((Nat.card {I : Ideal (𝓞 M) // absNorm I = n} : ℝ) : ℂ)) (s : ℂ) := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun _ ↦ Nat.cast_nonneg _)
    zero_le_one hs
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using nsg_tendsto_sum_card_div M)

private lemma nsg_summable_rterm {s : ℝ} (hs : 1 < s) : Summable (nsgRTerm M s) := by
  have h := nsg_LSeriesSummable M hs
  rw [LSeriesSummable] at h
  have hfun : LSeries.term (fun n ↦ ((Nat.card {I : Ideal (𝓞 M) // absNorm I = n} : ℝ) : ℂ))
      (s : ℂ) = fun n ↦ (nsgRTerm M s n : ℂ) := by
    funext n
    rw [← nsg_term_eq]
    simp only [Complex.ofReal_natCast]
  rw [hfun] at h
  exact Complex.summable_ofReal.mp h

private lemma nsg_dedekindZeta_ofReal (s : ℝ) :
    dedekindZeta M (s : ℂ) = ((∑' n, nsgRTerm M s n : ℝ) : ℂ) := by
  rw [dedekindZeta, LSeries, Complex.ofReal_tsum]
  exact tsum_congr (nsg_term_eq M s)

private lemma nsg_norm_dedekindZeta {s : ℝ} :
    ‖dedekindZeta M (s : ℂ)‖ = ∑' n, nsgRTerm M s n := by
  rw [nsg_dedekindZeta_ofReal M s, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg (nsgRTerm_nonneg M s))]

private lemma nsg_card_filter_absNorm_le (T : Finset (Ideal (𝓞 M))) (n : ℕ) :
    (T.filter (fun I ↦ absNorm I = n)).card ≤ Nat.card {I : Ideal (𝓞 M) // absNorm I = n} := by
  classical
  have hfin : Finite {I : Ideal (𝓞 M) // absNorm I = n} := finite_setOf_absNorm_eq n
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective
    (fun I : (T.filter (fun I ↦ absNorm I = n)) ↦ ⟨I.1, (Finset.mem_filter.mp I.2).2⟩) ?_
  intro I J h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext h

private lemma nsg_sum_absNorm_le_norm_zeta {s : ℝ} (hs : 1 < s) (T : Finset (Ideal (𝓞 M))) :
    ∑ I ∈ T, ((absNorm I : ℝ) ^ s)⁻¹ ≤ ‖dedekindZeta M (s : ℂ)‖ := by
  classical
  rw [nsg_norm_dedekindZeta M]
  have h0 : (0 : ℝ) ^ s = 0 := Real.zero_rpow (by linarith)
  calc ∑ I ∈ T, ((absNorm I : ℝ) ^ s)⁻¹
      = ∑ n ∈ T.image absNorm, ((T.filter (fun I ↦ absNorm I = n)).card : ℝ) * ((n : ℝ) ^ s)⁻¹ := by
        rw [Finset.sum_comp (fun n : ℕ ↦ ((n : ℝ) ^ s)⁻¹) (fun I : Ideal (𝓞 M) ↦ absNorm I)]
        simp only [nsmul_eq_mul]
    _ ≤ ∑ n ∈ T.image absNorm, nsgRTerm M s n := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        rcases eq_or_ne n 0 with rfl | hn
        · simp [nsgRTerm, h0]
        · rw [nsgRTerm, if_neg hn, div_eq_mul_inv]
          have h1 : ((T.filter (fun I ↦ absNorm I = n)).card : ℝ)
              ≤ (Nat.card {I : Ideal (𝓞 M) // absNorm I = n} : ℝ) := by
            exact_mod_cast nsg_card_filter_absNorm_le M T n
          have h2 : (0 : ℝ) ≤ ((n : ℝ) ^ s)⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_right h1 h2
    _ ≤ ∑' n, nsgRTerm M s n :=
        (nsg_summable_rterm M hs).sum_le_tsum _ (fun n _ ↦ nsgRTerm_nonneg M s n)

omit [NumberField M] in

private lemma nsg_prod_le_iff (S : Finset (Ideal (𝓞 M))) (hS : ∀ P ∈ S, P.IsMaximal)
    {T : Finset (Ideal (𝓞 M))} (hT : T ⊆ S) {Q : Ideal (𝓞 M)} (hQ : Q ∈ S) :
    ∏ P ∈ T, P ≤ Q ↔ Q ∈ T := by
  constructor
  · intro h
    obtain ⟨P, hP, hPQ⟩ := ((hS Q hQ).isPrime.prod_le).mp h
    have hPQ' : P = Q := (hS P (hT hP)).eq_of_le (hS Q hQ).ne_top hPQ
    exact hPQ' ▸ hP
  · intro h
    exact Ideal.prod_le_inf.trans (Finset.inf_le h)

omit [NumberField M] in
private lemma nsg_prod_injOn (S : Finset (Ideal (𝓞 M))) (hS : ∀ P ∈ S, P.IsMaximal) :
    Set.InjOn (fun T : Finset (Ideal (𝓞 M)) ↦ ∏ P ∈ T, P) (S.powerset : Set (Finset _)) := by
  intro T₁ h₁ T₂ h₂ h
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at h₁ h₂
  ext Q
  constructor
  · intro hQ
    have hQS : Q ∈ S := h₁ hQ
    have : ∏ P ∈ T₂, P ≤ Q := by
      have h' : ∏ P ∈ T₁, P ≤ Q := (nsg_prod_le_iff M S hS h₁ hQS).mpr hQ
      simpa only [h] using h'
    exact (nsg_prod_le_iff M S hS h₂ hQS).mp this
  · intro hQ
    have hQS : Q ∈ S := h₂ hQ
    have : ∏ P ∈ T₁, P ≤ Q := by
      have h' : ∏ P ∈ T₂, P ≤ Q := (nsg_prod_le_iff M S hS h₂ hQS).mpr hQ
      simpa only [← h] using h'
    exact (nsg_prod_le_iff M S hS h₁ hQS).mp this

private lemma nsg_prod_one_add_le (S : Finset (Ideal (𝓞 M))) (hS : ∀ P ∈ S, P.IsMaximal)
    {s : ℝ} (hs : 1 < s) :
    ∏ P ∈ S, (1 + ((absNorm P : ℝ) ^ s)⁻¹) ≤ ‖dedekindZeta M (s : ℂ)‖ := by
  classical
  rw [Finset.prod_one_add]
  have hT : ∀ T ∈ S.powerset,
      ∏ P ∈ T, ((absNorm P : ℝ) ^ s)⁻¹ = ((absNorm (∏ P ∈ T, P) : ℝ) ^ s)⁻¹ := by
    intro T _
    rw [map_prod, Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ ↦ Nat.cast_nonneg _),
      Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl hT]
  calc ∑ T ∈ S.powerset, ((absNorm (∏ P ∈ T, P) : ℝ) ^ s)⁻¹
      = ∑ I ∈ S.powerset.image (fun T ↦ ∏ P ∈ T, P), ((absNorm I : ℝ) ^ s)⁻¹ :=
        (Finset.sum_image (f := fun I : Ideal (𝓞 M) ↦ ((absNorm I : ℝ) ^ s)⁻¹)
          (nsg_prod_injOn M S hS)).symm
    _ ≤ ‖dedekindZeta M (s : ℂ)‖ := nsg_sum_absNorm_le_norm_zeta M hs _

private lemma nsg_sub_sq_le_log {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 ≤ Real.log (1 + x) := by
  have h1 : 0 < 1 + x := by positivity
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have key : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1]
    nlinarith [pow_nonneg hx 3]
  linarith

private lemma nsg_sum_primes_le_log (S : Finset (Ideal (𝓞 M))) (hS : ∀ P ∈ S, P.IsMaximal)
    {s : ℝ} (hs : 1 < s) :
    ∑ P ∈ S, ((absNorm P : ℝ) ^ s)⁻¹ ≤
      Real.log ‖dedekindZeta M (s : ℂ)‖ + ‖dedekindZeta M ((2 : ℝ) : ℂ)‖ := by

  have hx0 : ∀ P ∈ S, 0 ≤ ((absNorm P : ℝ) ^ s)⁻¹ := fun P _ ↦ by positivity

  have hprodpos : 0 < ∏ P ∈ S, (1 + ((absNorm P : ℝ) ^ s)⁻¹) :=
    Finset.prod_pos fun P hP ↦ by positivity
  have hlog : ∑ P ∈ S, Real.log (1 + ((absNorm P : ℝ) ^ s)⁻¹) ≤
      Real.log ‖dedekindZeta M (s : ℂ)‖ := by
    rw [← Real.log_prod (fun P hP ↦ (by positivity : (1 + ((absNorm P : ℝ) ^ s)⁻¹) ≠ 0))]
    exact Real.log_le_log hprodpos (nsg_prod_one_add_le M S hS hs)

  have hsq : ∑ P ∈ S, (((absNorm P : ℝ) ^ s)⁻¹) ^ 2 ≤ ‖dedekindZeta M ((2 : ℝ) : ℂ)‖ := by
    refine le_trans (Finset.sum_le_sum fun P hP ↦ ?_)
      (nsg_sum_absNorm_le_norm_zeta M one_lt_two S)

    rcases Nat.eq_zero_or_pos (absNorm P) with h0 | hpos
    · simp [h0, Real.zero_rpow (by linarith : s ≠ 0), Real.zero_rpow (two_ne_zero)]
    · have hN : (1 : ℝ) ≤ (absNorm P : ℝ) := by exact_mod_cast hpos
      rw [← Real.rpow_natCast, ← Real.inv_rpow (by positivity), ← Real.rpow_mul (by positivity),
        Real.inv_rpow (by positivity)]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)

  have hmain : ∑ P ∈ S, ((absNorm P : ℝ) ^ s)⁻¹ ≤
      ∑ P ∈ S, (Real.log (1 + ((absNorm P : ℝ) ^ s)⁻¹) + (((absNorm P : ℝ) ^ s)⁻¹) ^ 2) :=
    Finset.sum_le_sum fun P hP ↦ by linarith [nsg_sub_sq_le_log (hx0 P hP)]
  rw [Finset.sum_add_distrib] at hmain
  linarith

private lemma nsg_eventually_log_norm_zeta_le :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      Real.log ‖dedekindZeta M (s : ℂ)‖ ≤ Real.log (s - 1)⁻¹ + C := by
  have h := (tendsto_sub_one_mul_dedekindZeta_nhdsGT M).norm
  set B : ℝ := ‖((dedekindZeta_residue M : ℝ) : ℂ)‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  have h1 : ∀ᶠ s : ℝ in 𝓝[>] 1, ‖((s : ℂ) - 1) * dedekindZeta M (s : ℂ)‖ < B :=
    h.eventually (eventually_lt_nhds (lt_add_one _))
  have h2 : ∀ᶠ s : ℝ in 𝓝[>] 1, s ∈ Set.Ioo (1 : ℝ) 2 := Ioo_mem_nhdsGT one_lt_two
  refine ⟨max (Real.log B) 0, ?_⟩
  filter_upwards [h1, h2] with s hs1 hs2
  have hs0 : 0 < s - 1 := by linarith [hs2.1]
  have hlogpos : 0 ≤ Real.log (s - 1)⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hs0).mpr (by linarith [hs2.2]))
  have hnorm1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hs0.le]
  rw [norm_mul, hnorm1] at hs1
  rcases (norm_nonneg (dedekindZeta M (s : ℂ))).eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact add_nonneg hlogpos (le_max_right _ _)
  · have hlt : ‖dedekindZeta M (s : ℂ)‖ < B * (s - 1)⁻¹ := by
      rw [← div_eq_mul_inv, lt_div_iff₀ hs0, mul_comm]
      exact hs1
    calc Real.log ‖dedekindZeta M (s : ℂ)‖
        ≤ Real.log (B * (s - 1)⁻¹) := Real.log_le_log hpos hlt.le
      _ = Real.log (s - 1)⁻¹ + Real.log B := by
          rw [Real.log_mul hB0.ne' (inv_ne_zero hs0.ne'), add_comm]
      _ ≤ Real.log (s - 1)⁻¹ + max (Real.log B) 0 := by gcongr; exact le_max_left _ _

end Analytic

section Composite

variable (K : Type*) [Field K] [NumberField K]

private theorem ncard_primesOver_le_finrank {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ((Ideal.span {(ℓ : ℤ)}).primesOver (𝓞 K)).ncard ≤ Module.finrank ℚ K := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hp0 : (Ideal.span {(ℓ : ℤ)}) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]; exact hℓ0
  haveI : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hℓ0).mpr (Nat.prime_iff_prime_int.mp hℓ)).isMaximal hp0
  calc ((Ideal.span {(ℓ : ℤ)}).primesOver (𝓞 K)).ncard
      = ∑ q : (Ideal.span {(ℓ : ℤ)}).primesOver (𝓞 K), 1 := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, ← Finset.card_univ, Finset.card_eq_sum_ones]
    _ ≤ ∑ q : (Ideal.span {(ℓ : ℤ)}).primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
        Finset.sum_le_sum fun q _ => by
          haveI := q.2.1
          exact Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero (q.1.ramificationIdx_pos ℤ).ne' (q.1.inertiaDeg_pos ℤ).ne')
    _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank _ _
    _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K

private lemma nsg_exists_prime_liesOver (P : Ideal (𝓞 K)) [hP : P.IsMaximal] :
    ∃ ℓ : ℕ, ℓ.Prime ∧ P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 ↦ Ideal.IsMaximal.ne_bot_of_isIntegral_int P
    (Ideal.eq_bot_of_comap_eq_bot (hp.trans (by simp [hp0])))
  have hprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp]
    infer_instance
  have hpP' : p ∈ P.under ℤ := by rw [hp]; exact Ideal.mem_span_singleton_self p
  have hpP : algebraMap ℤ (𝓞 K) p ∈ P := Ideal.mem_comap.mp hpP'
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  have hprime' : Prime (p.natAbs : ℤ) := Nat.prime_iff_prime_int.mp (Int.prime_iff_natAbs_prime.mp hprime)
  refine (Ideal.liesOver_span_iff hP.ne_top hprime').mpr ?_
  exact P.mem_of_dvd (map_dvd (algebraMap ℤ (𝓞 K)) p.associated_natAbs.dvd) hpP

private lemma nsg_composite_facts (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hN : ¬ (absNorm P).Prime) :
    ((absNorm P).minFac).Prime ∧ P ∈ (Ideal.span {((absNorm P).minFac : ℤ)}).primesOver (𝓞 K) ∧
      (absNorm P).minFac ^ 2 ≤ absNorm P := by
  obtain ⟨ℓ, hℓ, hover⟩ := nsg_exists_prime_liesOver K P
  have hpow := Ideal.absNorm_eq_pow_inertiaDeg' P hℓ
  set f := (Ideal.span {(ℓ : ℤ)}).inertiaDeg' P with hf
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at hpow
    exact hP.ne_top hpow
  have hf1 : f ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hpow
    exact hN (hpow ▸ hℓ)
  have hf2 : 2 ≤ f := by omega
  have hmin : (absNorm P).minFac = ℓ := by rw [hpow, Nat.pow_minFac hf0, hℓ.minFac_eq]
  rw [hmin]
  exact ⟨hℓ, ⟨hP.isPrime, hover⟩, hpow ▸ Nat.pow_le_pow_right hℓ.pos hf2⟩

private lemma nsg_sum_composite_le (U : Finset (Ideal (𝓞 K)))
    (hU : ∀ P ∈ U, P.IsMaximal ∧ ¬ (absNorm P).Prime) {s : ℝ} (hs : 1 < s) :
    ∑ P ∈ U, ((absNorm P : ℝ) ^ s)⁻¹ ≤
      (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹ := by
  classical
  have hsum2 : Summable (fun m : ℕ ↦ ((m : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr one_lt_two

  have hterm : ∀ P ∈ U, ((absNorm P : ℝ) ^ s)⁻¹ ≤ ((((absNorm P).minFac : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro P hP
    haveI := (hU P hP).1
    obtain ⟨hℓ, -, hle⟩ := nsg_composite_facts K P (hU P hP).2
    have hN1 : (1 : ℝ) ≤ (absNorm P : ℝ) := by
      have := hℓ.one_lt.le.trans ((Nat.le_self_pow two_ne_zero _).trans hle)
      exact_mod_cast this
    have hℓ0 : (0 : ℝ) < (((absNorm P).minFac : ℕ) : ℝ) := by exact_mod_cast hℓ.pos
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    calc ((((absNorm P).minFac : ℕ) : ℝ) ^ 2) = (((absNorm P).minFac ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (absNorm P : ℝ) := by exact_mod_cast hle
      _ = (absNorm P : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (absNorm P : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hN1 hs.le

  have hfib : ∀ ℓ ∈ U.image (fun P ↦ (absNorm P).minFac),
      ((U.filter (fun P ↦ (absNorm P).minFac = ℓ)).card : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    intro ℓ hℓU
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hℓU
    haveI := (hU P₀ hP₀).1
    obtain ⟨hℓ, -, -⟩ := nsg_composite_facts K P₀ (hU P₀ hP₀).2
    have hsub : (↑(U.filter (fun P ↦ (absNorm P).minFac = (absNorm P₀).minFac)) : Set (Ideal (𝓞 K)))
        ⊆ (Ideal.span {(((absNorm P₀).minFac : ℕ) : ℤ)}).primesOver (𝓞 K) := by
      intro P hP
      rw [Finset.mem_coe, Finset.mem_filter] at hP
      haveI := (hU P hP.1).1
      obtain ⟨-, hmem, -⟩ := nsg_composite_facts K P (hU P hP.1).2
      rw [hP.2] at hmem
      exact hmem
    haveI : (Ideal.span {(((absNorm P₀).minFac : ℕ) : ℤ)}).IsMaximal :=
      (Nat.prime_iff_prime_int.mp hℓ).isMaximal_span_singleton
    have hfin := IsDedekindDomain.primesOver_finite (Ideal.span {(((absNorm P₀).minFac : ℕ) : ℤ)}) (𝓞 K)
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at h1
    exact_mod_cast h1.trans (ncard_primesOver_le_finrank K hℓ)
  calc ∑ P ∈ U, ((absNorm P : ℝ) ^ s)⁻¹
      ≤ ∑ P ∈ U, ((((absNorm P).minFac : ℕ) : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ = ∑ ℓ ∈ U.image (fun P ↦ (absNorm P).minFac),
          ((U.filter (fun P ↦ (absNorm P).minFac = ℓ)).card : ℝ) * (((ℓ : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_comp (fun ℓ : ℕ ↦ (((ℓ : ℕ) : ℝ) ^ 2)⁻¹) (fun P : Ideal (𝓞 K) ↦ (absNorm P).minFac)]
        simp only [nsmul_eq_mul]
    _ ≤ ∑ ℓ ∈ U.image (fun P ↦ (absNorm P).minFac), (Module.finrank ℚ K : ℝ) * (((ℓ : ℕ) : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun ℓ hℓ ↦ ?_
        exact mul_le_mul_of_nonneg_right (hfib ℓ hℓ) (by positivity)
    _ = (Module.finrank ℚ K : ℝ) * ∑ ℓ ∈ U.image (fun P ↦ (absNorm P).minFac), (((ℓ : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹ := by
        gcongr
        exact hsum2.sum_le_tsum _ (fun m _ ↦ by positivity)

end Composite

section Tail

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

omit [NumberField M] [IsGalois K M] in

private lemma nsg_mem_S1_iff (P : Ideal (𝓞 K)) :
    P ∈ nsgS1 K M ↔ P.IsMaximal ∧ (IsSplitPrime K M P ∨ ¬ (absNorm P).Prime) := by
  simp only [nsgS1, nsgPrimes, nsgT1, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
  constructor
  · rintro ⟨hmax, h⟩
    refine ⟨hmax, ?_⟩
    by_cases hpr : (absNorm P).Prime
    · exact Or.inl (h hmax hpr)
    · exact Or.inr hpr
  · rintro ⟨hmax, h⟩
    refine ⟨hmax, fun _ hpr ↦ ?_⟩
    rcases h with h | h
    · exact h
    · exact absurd hpr h

omit [IsGalois K M] in

private lemma nsg_summable_on_set (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable fun v : S ↦ ((absNorm v.1 : ℝ) ^ s)⁻¹ := by
  classical
  refine summable_of_sum_le (fun v ↦ (by positivity : (0 : ℝ) ≤ ((absNorm v.1 : ℝ) ^ s)⁻¹))
    (c := ‖dedekindZeta K (s : ℂ)‖) fun u ↦ ?_
  calc ∑ v ∈ u, ((absNorm v.1 : ℝ) ^ s)⁻¹
      = ∑ P ∈ u.image Subtype.val, ((absNorm P : ℝ) ^ s)⁻¹ :=
        (Finset.sum_image (f := fun P : Ideal (𝓞 K) ↦ ((absNorm P : ℝ) ^ s)⁻¹)
          (Subtype.val_injective.injOn)).symm
    _ ≤ ‖dedekindZeta K (s : ℂ)‖ := nsg_sum_absNorm_le_norm_zeta K hs _

omit [NumberField M] [IsGalois K M] in
private lemma nsg_tail_summable (s : ℝ) (hs : 1 < s) :
    Summable fun v : nsgS1 K M ↦ ((absNorm v.1 : ℝ) ^ s)⁻¹ :=
  nsg_summable_on_set K (nsgS1 K M) hs

private lemma nsg_tail_bound_explicit (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q)
    (hdeg : Module.finrank K M = q) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      (∑' v : nsgS1 K M, ((absNorm v.1 : ℝ) ^ s)⁻¹) ≤ (q : ℝ)⁻¹ * Real.log (s - 1)⁻¹ + C := by
  classical
  obtain ⟨CA, hA⟩ := NumberField.tsum_split_degOne_le K M q hq h3q hdeg
  obtain ⟨CM, hM⟩ := nsg_eventually_log_norm_zeta_le M
  set Ccomp : ℝ := (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹ with hCcomp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  refine ⟨(q : ℝ)⁻¹ * CM + CA + Ccomp, ?_⟩
  filter_upwards [hM, self_mem_nhdsWithin] with s hMs hs1
  have hs : 1 < s := hs1

  refine Real.tsum_le_of_sum_le
    (fun v ↦ (by positivity : (0 : ℝ) ≤ ((absNorm v.1 : ℝ) ^ s)⁻¹)) fun u ↦ ?_

  set U : Finset (Ideal (𝓞 K)) := u.image Subtype.val with hUdef
  have hUmem : ∀ P ∈ U, P ∈ nsgS1 K M := by
    intro P hP
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hP
    exact v.2
  have hsumU : ∑ v ∈ u, ((absNorm v.1 : ℝ) ^ s)⁻¹ = ∑ P ∈ U, ((absNorm P : ℝ) ^ s)⁻¹ :=
    (Finset.sum_image (f := fun P : Ideal (𝓞 K) ↦ ((absNorm P : ℝ) ^ s)⁻¹)
      (Subtype.val_injective.injOn)).symm
  rw [hsumU, ← Finset.sum_filter_add_sum_filter_not U (IsSplitPrime K M)]

  have hsplit : ∑ P ∈ U.filter (IsSplitPrime K M), ((absNorm P : ℝ) ^ s)⁻¹ ≤
      (q : ℝ)⁻¹ * Real.log ‖dedekindZeta M s‖ + CA := by
    refine le_trans ?_ (hA s hs)
    have hsumm : Summable fun 𝔩 : {I : Ideal (𝓞 K) // IsSplitPrime K M I} ↦
        ((absNorm (𝔩 : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ :=
      nsg_summable_on_set K {I : Ideal (𝓞 K) | IsSplitPrime K M I} hs
    rw [← Finset.subtype_map (IsSplitPrime K M), Finset.sum_map]
    exact hsumm.sum_le_tsum (U.subtype (IsSplitPrime K M)) (fun 𝔩 _ ↦ by positivity)

  have hcomp : ∑ P ∈ U.filter (fun P ↦ ¬ IsSplitPrime K M P), ((absNorm P : ℝ) ^ s)⁻¹ ≤ Ccomp := by
    refine nsg_sum_composite_le K _ (fun P hP ↦ ?_) hs
    rw [Finset.mem_filter] at hP
    obtain ⟨hmax, h⟩ := (nsg_mem_S1_iff K M P).mp (hUmem P hP.1)
    exact ⟨hmax, h.resolve_left hP.2⟩

  have hlog : (q : ℝ)⁻¹ * Real.log ‖dedekindZeta M s‖ ≤
      (q : ℝ)⁻¹ * Real.log (s - 1)⁻¹ + (q : ℝ)⁻¹ * CM := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hMs (inv_nonneg.mpr hq0.le)
  linarith

private lemma nsg_tail_bound (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q)
    (hdeg : Module.finrank K M = q) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 1,
      nsgTail K (nsgS1 K M) s ≤ (q : ℝ)⁻¹ * Real.log (s - 1)⁻¹ + C := by
  obtain ⟨C, hC⟩ := nsg_tail_bound_explicit K M q hq h3q hdeg
  exact ⟨C, by simpa only [nsgTail, nsgWr] using hC⟩

end Tail

section Bridge

variable (K : Type*) [Field K] [NumberField K]

private lemma nsg_summable_master {s : ℝ} (hs : 1 < s) :
    Summable fun I : {I : Ideal (𝓞 K) // I ≠ 0} => nsgWr K s I.1 :=
  nsg_summable_on_set K {I : Ideal (𝓞 K) | I ≠ 0} hs

open scoped Classical in

private noncomputable def nsgFib (n : ℕ) : Finset (Ideal (𝓞 K))⁰ :=
  ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset).subtype (· ∈ (Ideal (𝓞 K))⁰)

private lemma nsg_mem_fib {n : ℕ} {I : (Ideal (𝓞 K))⁰} : I ∈ nsgFib K n ↔ absNorm I.1 = n := by
  simp [nsgFib]

private lemma nsg_summable_twisted (f : (Ideal (𝓞 K))⁰ → ℂ) (hf : ∀ I, ‖f I‖ ≤ 1) {s : ℝ}
    (hs : 1 < s) :
    Summable fun I : (Ideal (𝓞 K))⁰ ↦
      f I * ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) := by
  have hsum : Summable fun I : (Ideal (𝓞 K))⁰ ↦ ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ :=
    nsg_summable_on_set K ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) hs
  refine Summable.of_norm_bounded hsum fun I ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖f I‖ * ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹
      ≤ 1 * ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ :=
        mul_le_mul_of_nonneg_right (hf I) (by positivity)
    _ = _ := one_mul _

private lemma nsg_fiber_sum_eq_term (f : (Ideal (𝓞 K))⁰ → ℂ) (s : ℝ) (n : ℕ) :
    ∑ I ∈ nsgFib K n, f I * ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) =
      LSeries.term (fun n ↦ ∑ I ∈ nsgFib K n, f I) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  ·
    rw [LSeries.term_zero]
    refine Finset.sum_eq_zero fun I hI ↦ ?_
    exact absurd ((nsg_mem_fib K).mp hI) (absNorm_ne_zero_of_nonZeroDivisors I)
  · rw [LSeries.term_of_ne_zero hn, Finset.sum_div]
    refine Finset.sum_congr rfl fun I hI ↦ ?_
    rw [(nsg_mem_fib K).mp hI, div_eq_mul_inv, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

private lemma nsg_hasSum_term (f : (Ideal (𝓞 K))⁰ → ℂ) (hf : ∀ I, ‖f I‖ ≤ 1) {s : ℝ}
    (hs : 1 < s) :
    HasSum (fun n ↦ LSeries.term (fun n ↦ ∑ I ∈ nsgFib K n, f I) s n)
      (∑' I : (Ideal (𝓞 K))⁰, f I * ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ)) := by
  classical
  have hsum := nsg_summable_twisted K f hf hs

  have hhas : HasSum ((fun I : (Ideal (𝓞 K))⁰ ↦
      f I * ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ)) ∘
        (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm (I : Ideal (𝓞 K)))))
      (∑' I : (Ideal (𝓞 K))⁰, f I * ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ)) := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm (I : Ideal (𝓞 K))))]
    exact ((Equiv.summable_iff _).mpr hsum).hasSum
  refine hhas.sigma fun n ↦ ?_

  have hfin : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} :=
    Fintype.ofFinset (nsgFib K n) (fun I ↦ nsg_mem_fib K)
  rw [← nsg_fiber_sum_eq_term, Finset.sum_subtype (nsgFib K n) (fun I ↦ nsg_mem_fib K)]
  exact hasSum_fintype _

private lemma nsg_ideal_tsum_eq_LSeries (f : (Ideal (𝓞 K))⁰ → ℂ) (hf : ∀ I, ‖f I‖ ≤ 1) {s : ℝ}
    (hs : 1 < s) :
    ∑' I : (Ideal (𝓞 K))⁰, f I * ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) =
      LSeries (fun n ↦ ∑ I ∈ nsgFib K n, f I) s := by
  rw [LSeries]
  exact (nsg_hasSum_term K f hf hs).tsum_eq.symm

private lemma nsg_card_fib {n : ℕ} (hn : n ≠ 0) :
    (nsgFib K n).card = Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  have hfin : Finite {I : Ideal (𝓞 K) // absNorm I = n} := Ideal.finite_setOf_absNorm_eq n
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  refine { toFun := fun I ↦ ⟨I.1.1, (nsg_mem_fib K).mp I.2⟩,
           invFun := fun I ↦ ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero (fun h ↦ hn ?_)⟩,
             (nsg_mem_fib K).mpr I.2⟩,
           left_inv := fun I ↦ by simp,
           right_inv := fun I ↦ by simp }
  rw [← I.2, h, Submodule.zero_eq_bot, absNorm_bot]

private lemma nsg_ideal_tsum_one_eq_zeta {s : ℝ} (hs : 1 < s) :
    ∑' I : (Ideal (𝓞 K))⁰, ((((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) =
      dedekindZeta K s := by
  have h := nsg_ideal_tsum_eq_LSeries K (fun _ ↦ 1) (fun _ ↦ by simp) hs
  simp only [one_mul] at h
  rw [h, dedekindZeta]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, nsg_card_fib K hn]

private noncomputable def nsgFibLe (n : ℕ) : Finset (Ideal (𝓞 K))⁰ :=
  (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).toFinset

private theorem nsg_mem_fibLe {n : ℕ} {I : (Ideal (𝓞 K))⁰} :
    I ∈ nsgFibLe K n ↔ Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n := by
  simp [nsgFibLe]

private lemma nsg_sum_Icc_fib {A : Type*} [AddCommMonoid A] (g : (Ideal (𝓞 K))⁰ → A) (n : ℕ) :
    ∑ k ∈ Icc 1 n, ∑ I ∈ nsgFib K k, g I = ∑ I ∈ nsgFibLe K n, g I := by
  classical
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext I
    simp only [Finset.mem_biUnion, Finset.mem_Icc, nsg_mem_fibLe, nsg_mem_fib]
    constructor
    · rintro ⟨k, ⟨-, hk⟩, hI⟩
      exact hI ▸ hk
    · intro hI
      exact ⟨absNorm I.1, ⟨Nat.one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors I), hI⟩,
        rfl⟩
  · intro k _ k' _ hne
    change Disjoint (nsgFib K k) (nsgFib K k')
    rw [Finset.disjoint_left]
    intro I hI hI'
    exact hne (((nsg_mem_fib K).mp hI).symm.trans ((nsg_mem_fib K).mp hI'))

private theorem nsg_LSeriesSummable_achi (f : (Ideal (𝓞 K))⁰ → ℂ) (hf : ∀ I, ‖f I‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => ∑ I ∈ nsgFib K n, f I) (s : ℂ) :=
  (nsg_hasSum_term K f hf hs).summable

private lemma nsg_card_norm_le_isBigO :
    (fun n : ℕ ↦ (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ))
      =O[atTop] fun n ↦ (n : ℝ) := by
  have hlim : Tendsto (fun n : ℕ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) / (n : ℝ)) atTop
        (𝓝 ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K * classNumber K) /
          (torsionOrder K * Real.sqrt |discr K|))) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le]
  have hO := isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1) (by simpa using hlim)
  simpa using hO

private theorem achi_norm_partial_bigO (χ : ClassGroup (𝓞 K) →* ℂ)
    (hnorm : ∀ c, ‖χ c‖ = 1) :
    (fun n => ∑ k ∈ Finset.Icc 1 n, ‖∑ I ∈ nsgFib K k, χ (ClassGroup.mk0 I)‖)
      =O[atTop] fun n => (n : ℝ) := by
  classical
  refine IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) (nsg_card_norm_le_isBigO K)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc ∑ k ∈ Finset.Icc 1 n, ‖∑ I ∈ nsgFib K k, χ (ClassGroup.mk0 I)‖
      ≤ ∑ k ∈ Finset.Icc 1 n, ∑ I ∈ nsgFib K k, ‖χ (ClassGroup.mk0 I)‖ :=
        Finset.sum_le_sum fun k _ ↦ norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ I ∈ nsgFib K k, (1 : ℝ) := by simp only [hnorm]
    _ = ((nsgFibLe K n).card : ℝ) := by
        rw [nsg_sum_Icc_fib K (fun _ ↦ (1 : ℝ)) n, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
        rw [nsgFibLe, ← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n),
          ← Nat.card_coe_set_eq]
        rfl

private lemma nsg_norm_zeta_eq_tsum {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K (s : ℂ)‖ = ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWr K s I.1 := by
  have h := nsg_ideal_tsum_one_eq_zeta K hs
  rw [← Complex.ofReal_tsum] at h
  rw [← h, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun I ↦ by positivity)]
  set e : (Ideal (𝓞 K))⁰ ≃ {I : Ideal (𝓞 K) // I ≠ 0} :=
    Equiv.subtypeEquivRight (fun I ↦ mem_nonZeroDivisors_iff_ne_zero) with he
  have hpt : ∀ c : (Ideal (𝓞 K))⁰,
      ((absNorm (c : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ = nsgWr K s (e c).1 := fun c ↦ rfl
  rw [tsum_congr hpt]
  exact Equiv.tsum_eq e (fun J ↦ nsgWr K s J.1)

private lemma nsg_zeta_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      c / (s - 1) ≤ ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWr K s I.1 := by
  have h := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hκ : 0 < dedekindZeta_residue K := dedekindZeta_residue_pos K
  have hnormκ : ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ = dedekindZeta_residue K := by
    rw [Complex.norm_real, Real.norm_of_nonneg hκ.le]
  rw [hnormκ] at h
  have h1 : ∀ᶠ s : ℝ in 𝓝[>] 1,
      dedekindZeta_residue K / 2 < ‖((s : ℂ) - 1) * dedekindZeta K (s : ℂ)‖ :=
    h.eventually (eventually_gt_nhds (by linarith))
  refine ⟨dedekindZeta_residue K / 2, by positivity, ?_⟩
  filter_upwards [h1, self_mem_nhdsWithin] with s hs hs1
  have hs' : 1 < s := hs1
  have hs0 : 0 < s - 1 := by linarith
  have hnorm1 : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hs0.le]
  rw [norm_mul, hnorm1] at hs
  rw [← nsg_norm_zeta_eq_tsum K hs', div_le_iff₀ hs0]
  calc dedekindZeta_residue K / 2 ≤ (s - 1) * ‖dedekindZeta K (s : ℂ)‖ := hs.le
    _ = ‖dedekindZeta K (s : ℂ)‖ * (s - 1) := mul_comm _ _

private lemma nsg_L_aux4_eq_aux2 (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℝ) :
    ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWc K χ s I.1 =
      ∑' I : (Ideal (𝓞 K))⁰, χ (ClassGroup.mk0 I) *
        ((((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) := by
  set e : (Ideal (𝓞 K))⁰ ≃ {I : Ideal (𝓞 K) // I ≠ 0} :=
    Equiv.subtypeEquivRight (fun I ↦ mem_nonZeroDivisors_iff_ne_zero) with he
  rw [← Equiv.tsum_eq e]
  refine tsum_congr fun I ↦ ?_
  have hI : (I : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hval : (e I).1 = (I : Ideal (𝓞 K)) := rfl
  rw [hval, nsgWc, nsgChi, dif_pos hI, nsgWr]

end Bridge

section Endgame

private lemma nsg_tendsto_log_inv_sub_one :
    Tendsto (fun s : ℝ ↦ Real.log (s - 1)⁻¹) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
        ((continuous_sub_right (1 : ℝ)).tendsto 1)
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ioi.mpr (sub_pos.mpr hs)
  exact Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h1)

private lemma nsg_endgame {a C B : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hlow : ∀ᶠ s : ℝ in 𝓝[>] 1, a * Real.log (s - 1)⁻¹ - C ≤ g s)
    (hup : ∀ᶠ s : ℝ in 𝓝[>] 1, g s ≤ B) : False := by
  have ht : Tendsto (fun s : ℝ ↦ a * Real.log (s - 1)⁻¹ - C) (𝓝[>] 1) atTop := by
    simp_rw [sub_eq_add_neg]
    exact tendsto_atTop_add_const_right _ _ (nsg_tendsto_log_inv_sub_one.const_mul_atTop ha)
  obtain ⟨s, h1, h2, h3⟩ := ((ht.eventually_gt_atTop B).and (hlow.and hup)).exists
  linarith

private lemma nsg_tendsto_inv_sub_one :
    Tendsto (fun s : ℝ ↦ (s - 1)⁻¹) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
        ((continuous_sub_right (1 : ℝ)).tendsto 1)
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ioi.mpr (sub_pos.mpr hs)
  exact tendsto_inv_nhdsGT_zero.comp h1

private lemma nsg_endgame_rpow {a c B : ℝ} (ha : 0 < a) (hc : 0 < c) {g : ℝ → ℝ}
    (hlow : ∀ᶠ s : ℝ in 𝓝[>] 1, c * ((s - 1)⁻¹ ^ a) ≤ g s)
    (hup : ∀ᶠ s : ℝ in 𝓝[>] 1, g s ≤ B) : False := by
  have ht : Tendsto (fun s : ℝ ↦ c * ((s - 1)⁻¹ ^ a)) (𝓝[>] 1) atTop :=
    ((tendsto_rpow_atTop ha).comp nsg_tendsto_inv_sub_one).const_mul_atTop hc
  obtain ⟨s, h1, h2, h3⟩ := ((ht.eventually_gt_atTop B).and (hlow.and hup)).exists
  linarith

private lemma nsg_rpow_combine {s : ℝ} (hs : 1 < s) (a : ℝ) :
    (s - 1)⁻¹ ^ (1 - a) * (s - 1) ^ a = (s - 1)⁻¹ ^ (1 - 2 * a) := by
  have h0 : 0 < s - 1 := by linarith
  have h0' : 0 < (s - 1)⁻¹ := inv_pos.mpr h0
  have ha : (s - 1) ^ a = (s - 1)⁻¹ ^ (-a) := by
    rw [Real.rpow_neg h0'.le, Real.inv_rpow h0.le, inv_inv]
  rw [ha, ← Real.rpow_add h0']
  congr 1
  ring

private lemma nsg_exp_pos {q : ℕ} (h3q : 3 ≤ q) : 0 < 1 - 2 * (q : ℝ)⁻¹ := by
  have hq : (3 : ℝ) ≤ q := by exact_mod_cast h3q
  have hq0 : (0 : ℝ) < q := by linarith
  rw [sub_pos, ← div_eq_mul_inv, div_lt_one hq0]
  linarith

end Endgame

end SplicePart1

section SplicePart2

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Finset"

section CharGeneral

variable {G : Type*} [CommGroup G] [Fintype G]

private lemma nsg_sum_char_eq_zero (χ : G →* ℂ) (hχ : χ ≠ 1) : ∑ c, χ c = 0 := by
  have hne : ¬ ∀ y, χ y = 1 := fun h ↦ hχ (MonoidHom.ext fun c ↦ by simpa using h c)
  obtain ⟨y, hy⟩ := not_forall.mp hne
  have hS : ∑ c, χ c = χ y * ∑ c, χ c := by
    rw [Finset.mul_sum]
    calc ∑ c, χ c = ∑ c, χ (y * c) := (Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun _ ↦ rfl).symm
      _ = ∑ c, χ y * χ c := Finset.sum_congr rfl fun c _ ↦ by rw [map_mul]
  have : (χ y - 1) * ∑ c, χ c = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hy
  · exact h

private lemma nsg_norm_char_eq_one (χ : G →* ℂ) (c : G) : ‖χ c‖ = 1 := by
  have hn : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have h : ‖χ c‖ ^ Fintype.card G = 1 := by
    rw [← norm_pow, ← map_pow, pow_card_eq_one, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h

private lemma nsg_exists_char_of_ne_top (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ χ : G →* ℂ, χ ≠ 1 ∧ (∀ c ∈ H, χ c = 1) ∧ ∀ c, ‖χ c‖ = 1 := by
  classical

  have hne : ¬ ∀ g : G, g ∈ H := fun h ↦ hH (eq_top_iff.mpr fun g _ ↦ h g)
  obtain ⟨g, hg⟩ := not_forall.mp hne
  have hfin : Finite (G ⧸ H) := inferInstance
  have ha : (QuotientGroup.mk' H g : G ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨φ, hφ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ H) ℂ ha
  refine ⟨(Units.coeHom ℂ).comp (φ.comp (QuotientGroup.mk' H)), ?_, ?_, ?_⟩
  · intro h1
    apply hφ
    have := DFunLike.congr_fun h1 g
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      MonoidHom.one_apply] at this
    exact Units.val_eq_one.mp this
  · intro c hc
    have hc1 : (QuotientGroup.mk c : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    simp [hc1]
  · intro c
    exact nsg_norm_char_eq_one _ c

end CharGeneral

section CharClassGroup

variable (K : Type*) [Field K] [NumberField K]

private lemma nsg_exists_char (H : Subgroup (ClassGroup (𝓞 K))) (hH : H ≠ ⊤) :
    ∃ χ : ClassGroup (𝓞 K) →* ℂ, χ ≠ 1 ∧ (∀ c ∈ H, χ c = 1) ∧ ∀ c, ‖χ c‖ = 1 :=
  nsg_exists_char_of_ne_top H hH

end CharClassGroup

end SplicePart2

section SplicePart3

p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors"
p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

section SplitArith

variable {K M}

namespace NumberField p2m_export "NumberField" "dedekindZeta_residue_pos discr mk RingOfIntegers.not_isField RingOfIntegers tendsto_sub_one_mul_dedekindZeta_nhdsGT dedekindZeta InfinitePlace Ideal.tendsto_norm_le_div_atTop₀ classNumber dedekindZeta_residue IsSplitPrime tsum_split_degOne_le exists_isBigO_card_absNorm_le_mk_eq_sub" namespace IsSplitPrime end NumberField.IsSplitPrime
namespace NumberField.IsSplitPrime
p2m_open_scoped "NumberField" in
omit [NumberField M] [IsGalois K M] in
private theorem _root_.NumberField.IsSplitPrime.ne_bot {𝔩 : Ideal (𝓞 K)} (h : IsSplitPrime K M 𝔩) :
    𝔩 ≠ ⊥ :=
  fun hb => h.2.1.ne_zero (absNorm_eq_zero_iff.mpr hb)

end NumberField.IsSplitPrime
p2m_export "" "NumberField.IsSplitPrime.ne_bot"
namespace NumberField.IsSplitPrime
p2m_open_scoped "NumberField" in
omit [NumberField M] [IsGalois K M] in
private theorem _root_.NumberField.IsSplitPrime.ncard_primesOver {𝔩 : Ideal (𝓞 K)} (h : IsSplitPrime K M 𝔩) :
    (primesOver 𝔩 (𝓞 M)).ncard = Module.finrank K M := by
  rw [← Nat.card_coe_set_eq]; exact h.2.2

end NumberField.IsSplitPrime
p2m_export "" "NumberField.IsSplitPrime.ncard_primesOver"
namespace NumberField.IsSplitPrime
p2m_open_scoped "NumberField" in

private theorem _root_.NumberField.IsSplitPrime.ef_eq_one {𝔩 : Ideal (𝓞 K)} (h : IsSplitPrime K M 𝔩) :
    ramificationIdxIn 𝔩 (𝓞 M) * inertiaDegIn 𝔩 (𝓞 M) = 1 := by
  haveI : 𝔩.IsMaximal := h.1
  have hef := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔩 (𝓞 M) (M ≃ₐ[K] M)
  rw [IsGaloisGroup.card_eq_finrank (M ≃ₐ[K] M) K M, ← h.ncard_primesOver] at hef
  have hg : 0 < (primesOver 𝔩 (𝓞 M)).ncard := h.ncard_primesOver ▸ Module.finrank_pos
  exact Nat.eq_of_mul_eq_mul_left hg (by rw [hef, Nat.mul_one])

end NumberField.IsSplitPrime
p2m_export "" "NumberField.IsSplitPrime.ef_eq_one"
namespace NumberField.IsSplitPrime
p2m_open_scoped "NumberField" in

private theorem _root_.NumberField.IsSplitPrime.absNorm_of_liesOver {𝔩 : Ideal (𝓞 K)} (h : IsSplitPrime K M 𝔩)
    (𝔓 : Ideal (𝓞 M)) [𝔓.IsPrime] [𝔓.LiesOver 𝔩] :
    absNorm 𝔓 = absNorm 𝔩 := by
  haveI : 𝔩.IsMaximal := h.1
  have hf : inertiaDeg' 𝔩 𝔓 = 1 := by
    haveI : 𝔓.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := 𝔩) 𝔓
    rw [inertiaDeg'_eq_inertiaDeg 𝔩 𝔓, ← inertiaDegIn_eq_inertiaDeg 𝔩 𝔓 (M ≃ₐ[K] M)]
    exact Nat.dvd_one.mp ⟨_, ((mul_comm _ _).trans h.ef_eq_one).symm⟩
  rw [absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓 𝔩 h.1.isPrime h.ne_bot, hf, pow_one]

end NumberField.IsSplitPrime
p2m_export "" "NumberField.IsSplitPrime.absNorm_of_liesOver"
namespace NumberField.IsSplitPrime
p2m_open_scoped "NumberField" in
private theorem _root_.NumberField.IsSplitPrime.absNorm_of_mem_primesOver {𝔩 : Ideal (𝓞 K)} (h : IsSplitPrime K M 𝔩)
    {𝔓 : Ideal (𝓞 M)} (h𝔓 : 𝔓 ∈ primesOver 𝔩 (𝓞 M)) :
    absNorm 𝔓 = absNorm 𝔩 :=
  haveI := h𝔓.1; haveI := h𝔓.2; h.absNorm_of_liesOver 𝔓

end NumberField.IsSplitPrime
p2m_export "" "NumberField.IsSplitPrime.absNorm_of_mem_primesOver"
omit [NumberField K] [NumberField M] [IsGalois K M] in

private theorem disjoint_primesOver_of_ne {𝔩 𝔩' : Ideal (𝓞 K)} [𝔩.IsMaximal] [𝔩'.IsMaximal]
    (hne : 𝔩 ≠ 𝔩') :
    Disjoint (primesOver 𝔩 (𝓞 M)) (primesOver 𝔩' (𝓞 M)) := by
  rw [Set.disjoint_iff]
  rintro 𝔓 ⟨⟨_, hl⟩, ⟨_, hl'⟩⟩
  exact hne ((𝔓.over_def 𝔩).trans (𝔓.over_def 𝔩').symm)

namespace NumberField.IsSplitPrime
p2m_open_scoped "NumberField" in

private theorem _root_.NumberField.IsSplitPrime.sum_primesOverFinset_inv_pow {𝔩 : Ideal (𝓞 K)}
    (h : IsSplitPrime K M 𝔩) (s : ℝ) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔩 (𝓞 M), ((absNorm P : ℝ) ^ s)⁻¹
      = (Module.finrank K M : ℝ) * ((absNorm 𝔩 : ℝ) ^ s)⁻¹ := by
  haveI := h.1
  rw [← h.ncard_primesOver, ← IsDedekindDomain.coe_primesOverFinset h.ne_bot (𝓞 M),
    Set.ncard_coe_finset, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [h.absNorm_of_mem_primesOver
    ((IsDedekindDomain.mem_primesOverFinset_iff h.ne_bot (𝓞 M)).mp hP)]

end NumberField.IsSplitPrime
p2m_export "" "NumberField.IsSplitPrime.sum_primesOverFinset_inv_pow"

private theorem nsg_sum_biUnion_primesOver (F : Finset {I : Ideal (𝓞 K) // IsSplitPrime K M I})
    (s : ℝ) :
    ∑ P ∈ F.biUnion (fun 𝔩 => IsDedekindDomain.primesOverFinset 𝔩.1 (𝓞 M)),
        ((absNorm P : ℝ) ^ s)⁻¹
      = (Module.finrank K M : ℝ) * ∑ 𝔩 ∈ F, ((absNorm 𝔩.1 : ℝ) ^ s)⁻¹ := by
  rw [Finset.sum_biUnion, Finset.mul_sum]
  · exact Finset.sum_congr rfl fun 𝔩 _ => 𝔩.2.sum_primesOverFinset_inv_pow s
  · rintro ⟨𝔩, h𝔩⟩ - ⟨𝔩', h𝔩'⟩ - hne
    haveI := h𝔩.1; haveI := h𝔩'.1
    refine Finset.disjoint_coe.mp ?_
    rw [IsDedekindDomain.coe_primesOverFinset h𝔩.ne_bot,
      IsDedekindDomain.coe_primesOverFinset h𝔩'.ne_bot]
    exact disjoint_primesOver_of_ne (fun he => hne (Subtype.ext he))

omit [IsGalois K M] in
private theorem nsg_isMaximal_of_mem_biUnion
    {F : Finset {I : Ideal (𝓞 K) // IsSplitPrime K M I}} {P : Ideal (𝓞 M)}
    (hP : P ∈ F.biUnion (fun 𝔩 => IsDedekindDomain.primesOverFinset 𝔩.1 (𝓞 M))) :
    P.IsMaximal := by
  obtain ⟨𝔩, -, hP𝔩⟩ := Finset.mem_biUnion.mp hP
  haveI := 𝔩.2.1
  exact isMaximal_of_mem_primesOver
    ((IsDedekindDomain.mem_primesOverFinset_iff 𝔩.2.ne_bot (𝓞 M)).mp hP𝔩)

end SplitArith

end SplicePart3

section SplicePart4

p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors"
p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal Filter Asymptotics Topology Finset"

variable (K : Type*) [Field K] [NumberField K]

section Abel

open scoped Classical

private noncomputable def nsgClsCount (c : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n ∧ ClassGroup.mk0 I = c}

private theorem nsg_uniform_lbound :
    ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧ ∀ c : ClassGroup (𝓞 K),
      (fun x : ℝ => (Nat.card {I : (Ideal (𝓞 K))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x ∧ ClassGroup.mk0 I = c} : ℝ)
        - (dedekindZeta_residue K / classNumber K) * x)
      =O[atTop] fun x => x ^ θ := by
  have hLB := NumberField.exists_isBigO_card_absNorm_le_mk_eq_sub K

  choose θc hθc hOc using hLB
  classical

  refine ⟨max (1/2) (Finset.univ.sup' Finset.univ_nonempty θc), ?_, ?_, ?_⟩
  · exact max_lt (by norm_num)
      (Finset.sup'_lt_iff Finset.univ_nonempty |>.mpr fun c _ => hθc c)
  · exact le_max_of_le_left (by norm_num)
  · intro c
    have hle : θc c ≤ max (1/2) (Finset.univ.sup' Finset.univ_nonempty θc) :=
      le_max_of_le_right (Finset.le_sup' θc (Finset.mem_univ c))
    refine (hOc c).trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [one_mul, Real.norm_rpow_of_nonneg (zero_le_one.trans hx),
      Real.norm_of_nonneg (zero_le_one.trans hx)]
    exact Real.rpow_le_rpow_of_exponent_le hx hle

private theorem achi_partial_bigO (χ : ClassGroup (𝓞 K) →* ℂ)
    (hχsum : ∑ c : ClassGroup (𝓞 K), χ c = 0) :
    ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
          ∑ I ∈ nsgFib K k, χ (ClassGroup.mk0 I)) =O[atTop] fun n => (n : ℝ) ^ θ := by
  obtain ⟨θ, hθ1, hθ0, hO⟩ := nsg_uniform_lbound K
  refine ⟨θ, hθ1, hθ0, ?_⟩
  set κ : ℝ := dedekindZeta_residue K / classNumber K
  set cnt : ClassGroup (𝓞 K) → ℝ → ℝ :=
    fun c x => (Nat.card {I : (Ideal (𝓞 K))⁰ //
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x ∧ ClassGroup.mk0 I = c} : ℝ) with hcnt

  have h1 : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, ∑ I ∈ nsgFib K k, χ (ClassGroup.mk0 I)
      = ∑ c : ClassGroup (𝓞 K), χ c * (cnt c n : ℂ) := by
    intro n; classical
    rw [nsg_sum_Icc_fib, ← Finset.sum_fiberwise_of_maps_to
      (g := fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : ∀ I ∈ (nsgFibLe K n).filter (fun I => ClassGroup.mk0 I = c),
        χ (ClassGroup.mk0 I) = χ c := fun I hI => by
      rw [(Finset.mem_filter.mp hI).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hseteq :
        ({I | I ∈ (nsgFibLe K n).filter (fun I => ClassGroup.mk0 I = c)} : Set (Ideal (𝓞 K))⁰)
          = {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)
              ∧ ClassGroup.mk0 I = c} := by
      ext I
      simp only [Finset.mem_filter, Set.mem_setOf_eq, nsg_mem_fibLe, Nat.cast_le]
    have hcard : ((nsgFibLe K n).filter (fun I => ClassGroup.mk0 I = c)).card
        = Nat.card {I : (Ideal (𝓞 K))⁰ //
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ) ∧ ClassGroup.mk0 I = c} := by
      rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq,
        show ((nsgFibLe K n).filter (fun I => ClassGroup.mk0 I = c) : Set (Ideal (𝓞 K))⁰)
          = {I | I ∈ (nsgFibLe K n).filter (fun I => ClassGroup.mk0 I = c)} from rfl,
        hseteq]
      rfl
    simp only [hcnt]
    rw [hcard]
    push_cast
    ring

  have h2 : ∀ n : ℕ, ∑ c : ClassGroup (𝓞 K), χ c * (cnt c n : ℂ)
      = ∑ c : ClassGroup (𝓞 K), χ c * ((cnt c n - κ * n : ℝ) : ℂ) := by
    intro n
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hχsum, zero_mul, sub_zero]

  simp only [h1, h2]
  rw [show (fun n : ℕ => ∑ c : ClassGroup (𝓞 K), χ c * ((cnt c n - κ * n : ℝ) : ℂ)) =
      ∑ c : ClassGroup (𝓞 K), (fun n : ℕ => χ c * ((cnt c n - κ * n : ℝ) : ℂ)) from
    (Finset.sum_fn _ _).symm]
  refine IsBigO.sum fun c _ => ?_
  have hOn : (fun n : ℕ => ((cnt c n - κ * n : ℝ) : ℂ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ θ := by
    refine Complex.isBigO_ofReal_left.mpr ?_
    have := (hO c).comp_tendsto tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, hcnt] using this
  exact hOn.const_mul_left (χ c)

private theorem nsg_LSeries_bounded_of_partial_bigO {f : ℕ → ℂ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hO : (fun n => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ θ)
    (hOnorm : (fun n => ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop] fun n => (n : ℝ)) :
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Set.Ioo (1:ℝ) 2 → ‖LSeries f s‖ ≤ C := by
  set Sf : ℕ → ℂ := fun n => ∑ k ∈ Finset.Icc 1 n, f k

  obtain ⟨C₀, hC₀⟩ := hO.bound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC₀

  set C₁ : ℝ := max C₀ ((Finset.range (N₀ + 1)).sup' ⟨0, Finset.mem_range.mpr N₀.succ_pos⟩
    fun k => ‖Sf k‖) with hC₁
  have hCpos : 0 ≤ C₁ :=
    le_max_of_le_right (Finset.le_sup'_of_le _ (Finset.mem_range.mpr N₀.succ_pos)
      (by simp [Sf]))
  have h_unif : ∀ n, 1 ≤ n → ‖Sf n‖ ≤ C₁ * (n : ℝ) ^ θ := by
    intro n hn
    rcases le_or_gt N₀ n with hle | hlt
    · calc ‖Sf n‖ ≤ C₀ * ‖(n : ℝ) ^ θ‖ := hN₀ n hle
        _ = C₀ * (n : ℝ) ^ θ := by
            rw [Real.norm_rpow_of_nonneg n.cast_nonneg, Real.norm_natCast]
        _ ≤ C₁ * (n : ℝ) ^ θ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.rpow_nonneg n.cast_nonneg _)
    · calc ‖Sf n‖ ≤ C₁ :=
            le_max_of_le_right
              (Finset.le_sup' (fun k => ‖Sf k‖)
                (Finset.mem_range.mpr (Nat.lt_succ_of_lt hlt)))
        _ = C₁ * 1 := (mul_one _).symm
        _ ≤ C₁ * (n : ℝ) ^ θ :=
            mul_le_mul_of_nonneg_left
              (Real.one_le_rpow (Nat.one_le_cast.mpr hn) hθ0) hCpos

  have hdom_int : MeasureTheory.IntegrableOn (fun t => C₁ * t ^ (θ - 2)) (Set.Ioi (1:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : θ - 2 < -1) one_pos).const_mul C₁
  have hdom_val : ∫ t in Set.Ioi (1:ℝ), C₁ * t ^ (θ - 2) = C₁ / (1 - θ) := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : θ - 2 < -1) one_pos,
      Real.one_rpow]
    have : θ - 2 + 1 = -(1 - θ) := by ring
    rw [this]
    field_simp

  refine ⟨2 * (C₁ / (1 - θ)), fun s ⟨hs1, hs2⟩ => ?_⟩
  have hOnorm' : (fun n => ∑ k ∈ Finset.Icc 1 n, ‖f k‖)
      =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hOnorm
  have hS : LSeriesSummable f s :=
    LSeriesSummable_of_sum_norm_bigO hOnorm' zero_le_one
      (show (1 : ℝ) < (s : ℂ).re by simpa using hs1)
  rw [LSeries_eq_mul_integral f hθ0
    (show θ < (s : ℂ).re by simpa using hθ1.trans hs1) hS hO]
  rw [norm_mul]
  have hs_norm : ‖(s : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hs1.le)]
    exact hs2.le
  refine mul_le_mul hs_norm ?_ (norm_nonneg _) (by norm_num)

  rw [← hdom_val]
  calc ‖∫ t in Set.Ioi (1:ℝ), Sf ⌊t⌋₊ * (t : ℂ) ^ (-((s : ℂ) + 1))‖
      ≤ ∫ t in Set.Ioi (1:ℝ), ‖Sf ⌊t⌋₊ * (t : ℂ) ^ (-((s : ℂ) + 1))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (1:ℝ), C₁ * t ^ (θ - 2) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) hdom_int ?_
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall fun t ht => ?_)
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hft : (1 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
        show ‖Sf ⌊t⌋₊ * (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤ C₁ * t ^ (θ - 2)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht1)]
        have hre : (-((s : ℂ) + 1)).re = -(s + 1) := by
          simp [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
        rw [hre]
        calc ‖Sf ⌊t⌋₊‖ * t ^ (-(s + 1))
            ≤ (C₁ * (⌊t⌋₊ : ℝ) ^ θ) * t ^ (-(s + 1)) :=
              mul_le_mul_of_nonneg_right (h_unif _ hft)
                (Real.rpow_nonneg (zero_le_one.trans ht1) _)
          _ ≤ (C₁ * t ^ θ) * t ^ (-(s + 1)) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (zero_le_one.trans ht1) _)
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans ht1)) hθ0)
                hCpos
          _ ≤ C₁ * t ^ (θ - 2) := by
              rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans_le ht1)]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hCpos

private theorem nsg_chiL_bound (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1)
    (hnorm : ∀ c, ‖χ c‖ = 1) :
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Set.Ioo (1:ℝ) 2 →
      ‖∑' I : (Ideal (𝓞 K))⁰,
          χ (ClassGroup.mk0 I)
            * ((((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹ : ℝ) : ℂ)‖ ≤ C := by
  have hχsum : ∑ c : ClassGroup (𝓞 K), χ c = 0 := nsg_sum_char_eq_zero χ hχ
  obtain ⟨θ, hθ1, hθ0, hO⟩ := achi_partial_bigO K χ hχsum
  obtain ⟨C, hC⟩ := nsg_LSeries_bounded_of_partial_bigO hθ0 hθ1 hO
    (achi_norm_partial_bigO K χ hnorm)
  refine ⟨C, fun s hs => ?_⟩
  rw [nsg_ideal_tsum_eq_LSeries K _ (fun I => (hnorm _).le) hs.1]
  exact hC s hs

end Abel

end SplicePart4

section SplicePart5

open UniqueFactorizationMonoid
open scoped ENNReal Classical

section NsgbApp

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal"
p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

omit [NumberField M] [IsGalois K M] in
private lemma nsgT1_subset_primes : nsgT1 K M ⊆ nsgPrimes K := fun _ hP => hP.1

omit [NumberField M] [IsGalois K M] in
private lemma nsgT1_union_S1 : nsgT1 K M ∪ nsgS1 K M = nsgPrimes K :=
  Set.union_diff_cancel (nsgT1_subset_primes K M)

omit [NumberField M] [IsGalois K M] in
private lemma nsgT1_disjoint_S1 : Disjoint (nsgT1 K M) (nsgS1 K M) :=
  Set.disjoint_sdiff_right

private lemma nsg_maximal_ne_bot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : P ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)

private lemma nsg_prime_of_mem_primes {P : Ideal (𝓞 K)} (hP : P ∈ nsgPrimes K) :
    Prime P :=
  Ideal.prime_of_isPrime (nsg_maximal_ne_bot K hP) hP.isPrime

private lemma nsg_memSupp_primes {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    MemSupp (nsgPrimes K) I := by
  refine ⟨hI, fun P hP => ?_⟩
  have hprime : Prime P := prime_of_normalized_factor P hP
  exact (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero

private lemma nsg_two_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    2 ≤ Ideal.absNorm P := by
  rcases Nat.lt_or_ge (Ideal.absNorm P) 2 with h | h
  · interval_cases h' : Ideal.absNorm P
    · exact absurd (Ideal.absNorm_eq_zero_iff.mp h') (nsg_maximal_ne_bot K hP)
    · exact absurd (Ideal.absNorm_eq_one_iff.mp h') hP.ne_top
  · exact h

private lemma nsgWr_nonneg (s : ℝ) (I : Ideal (𝓞 K)) : 0 ≤ nsgWr K s I := by
  unfold nsgWr
  positivity

private noncomputable def nsgWe (s : ℝ) (I : Ideal (𝓞 K)) : ℝ≥0∞ :=
  ENNReal.ofReal (nsgWr K s I)

private lemma nsgWr_mul {I J : Ideal (𝓞 K)} (_ : I ≠ 0) (_ : J ≠ 0) (s : ℝ) :
    nsgWr K s (I * J) = nsgWr K s I * nsgWr K s J := by
  unfold nsgWr
  rw [_root_.map_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), mul_inv]

private lemma nsgWe_mul {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) (s : ℝ) :
    nsgWe K s (I * J) = nsgWe K s I * nsgWe K s J := by
  unfold nsgWe
  rw [nsgWr_mul K hI hJ, ENNReal.ofReal_mul (nsgWr_nonneg K s I)]

private lemma nsgChi_mul (χ : ClassGroup (𝓞 K) →* ℂ) {I J : Ideal (𝓞 K)}
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    nsgChi K χ (I * J) = nsgChi K χ I * nsgChi K χ J := by
  have hIJ : I * J ≠ 0 := mul_ne_zero hI hJ
  have hsub : (⟨I * J, mem_nonZeroDivisors_of_ne_zero hIJ⟩ : (Ideal (𝓞 K))⁰) =
      ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ * ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ :=
    rfl
  simp only [nsgChi, dif_pos hI, dif_pos hJ, dif_pos hIJ, hsub, _root_.map_mul]

private lemma nsgWc_mul (χ : ClassGroup (𝓞 K) →* ℂ) {I J : Ideal (𝓞 K)}
    (hI : I ≠ 0) (hJ : J ≠ 0) (s : ℝ) :
    nsgWc K χ s (I * J) = nsgWc K χ s I * nsgWc K χ s J := by
  unfold nsgWc
  rw [nsgChi_mul K χ hI hJ, nsgWr_mul K hI hJ]
  push_cast
  ring

private lemma nsgWr_one (s : ℝ) : nsgWr K s 1 = 1 := by
  unfold nsgWr
  simp [Ideal.absNorm_top]

private lemma nsgWc_one (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℝ) : nsgWc K χ s 1 = 1 := by
  unfold nsgWc nsgChi
  rw [dif_pos one_ne_zero]
  have h1 : (⟨(1 : Ideal (𝓞 K)), mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ :
      (Ideal (𝓞 K))⁰) = 1 := rfl
  rw [h1]
  simp only [_root_.map_one, nsgWr_one, Complex.ofReal_one, one_mul]

end NsgbApp

section NsgbALower

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal"
p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

private lemma nsgWr_pow (s : ℝ) (v : Ideal (𝓞 K)) (k : ℕ) :
    nsgWr K s (v ^ k) = nsgWr K s v ^ k := by
  unfold nsgWr
  rw [_root_.map_pow, Nat.cast_pow, ← Real.rpow_natCast ((Ideal.absNorm v : ℝ)) k,
    ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm, Real.rpow_mul (Nat.cast_nonneg _),
    Real.rpow_natCast, inv_pow]

private lemma nsgWr_le_half {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {s : ℝ} (hs : 1 ≤ s) :
    nsgWr K s P ≤ 1 / 2 := by
  unfold nsgWr
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by
    exact_mod_cast nsg_two_le_absNorm K hP
  have h2s : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ s := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ s := Real.rpow_le_rpow_of_exponent_le one_le_two hs
      _ ≤ (Ideal.absNorm P : ℝ) ^ s :=
          Real.rpow_le_rpow (by norm_num) h2 (le_trans zero_le_one hs)
  rw [one_div]
  exact inv_anti₀ (by norm_num) h2s

private lemma nsgWr_sq_le {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {s : ℝ} (hs : 1 ≤ s) :
    nsgWr K s P ^ 2 ≤ nsgWr K 2 P := by
  unfold nsgWr
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by
    have := nsg_two_le_absNorm K hP
    exact_mod_cast le_trans (by norm_num) this
  rw [inv_pow]
  refine inv_anti₀ (by positivity) ?_
  calc (Ideal.absNorm P : ℝ) ^ (2 : ℝ)
      ≤ (Ideal.absNorm P : ℝ) ^ (2 * s) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = ((Ideal.absNorm P : ℝ) ^ s) ^ 2 := by
        rw [← Real.rpow_natCast ((Ideal.absNorm P : ℝ) ^ s) 2,
          ← Real.rpow_mul (by positivity)]
        norm_num [mul_comm]

private lemma nsg_one_sub_inv_le_exp {x : ℝ} (_ : 0 ≤ x) (h2 : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (x + 2 * x ^ 2) := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hkey : (1 - x)⁻¹ = 1 + x / (1 - x) := by
    field_simp
    ring
  have hdiv : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ h1x]
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0:ℝ) ≤ 1 - 2 * x)]
  calc (1 - x)⁻¹ = x / (1 - x) + 1 := by rw [hkey]; ring
    _ ≤ Real.exp (x / (1 - x)) := Real.add_one_le_exp _
    _ ≤ Real.exp (x + 2 * x ^ 2) := Real.exp_le_exp.mpr hdiv

private lemma nsg_geom_ennreal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {s : ℝ}
    (hs : 1 ≤ s) :
    (∑' k : ℕ, nsgWe K s (P ^ k)) = ENNReal.ofReal (1 - nsgWr K s P)⁻¹ := by
  have hx0 : 0 ≤ nsgWr K s P := nsgWr_nonneg K s P
  have hx1 : nsgWr K s P < 1 := lt_of_le_of_lt (nsgWr_le_half K hP hs) (by norm_num)
  have hsummable : Summable fun k : ℕ => nsgWr K s P ^ k :=
    summable_geometric_of_lt_one hx0 hx1
  calc (∑' k : ℕ, nsgWe K s (P ^ k))
      = ∑' k : ℕ, ENNReal.ofReal (nsgWr K s P ^ k) := by
        refine tsum_congr fun k => ?_
        rw [nsgWe, nsgWr_pow]
    _ = ENNReal.ofReal (∑' k : ℕ, nsgWr K s P ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hx0 k) hsummable).symm
    _ = ENNReal.ofReal (1 - nsgWr K s P)⁻¹ := by
        rw [tsum_geometric_of_lt_one hx0 hx1]

private lemma nsg_summable_subset {S : Set (Ideal (𝓞 K))} (hS : S ⊆ nsgPrimes K)
    {s : ℝ} (hs : 1 < s) :
    Summable fun v : S => nsgWr K s v.1 := by
  have hmaster := nsg_summable_master K hs
  have hinj : Function.Injective
      (fun v : S => (⟨v.1, nsg_maximal_ne_bot K (hS v.2)⟩ : {I : Ideal (𝓞 K) // I ≠ 0})) := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    simpa [Subtype.ext_iff] using h
  have := hmaster.comp_injective hinj
  simpa only [Function.comp_def] using this

private noncomputable def nsgZ2 : ℝ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWr K 2 I.1

private lemma nsg_sum_le_tail {S : Set (Ideal (𝓞 K))} (hS : S ⊆ nsgPrimes K)
    {F : Finset (Ideal (𝓞 K))} (hF : ↑F ⊆ S) {s : ℝ} (hs : 1 < s)
    {g : Ideal (𝓞 K) → ℝ} (_ : ∀ v, 0 ≤ g v) (hgle : ∀ v ∈ S, g v ≤ nsgWr K s v) :
    ∑ v ∈ F, g v ≤ nsgTail K S s := by
  classical
  have hsum : Summable fun v : S => nsgWr K s v.1 := nsg_summable_subset K hS hs

  let F' : Finset S := F.attach.image fun v => ⟨v.1, hF v.2⟩
  have hinj : ∀ v ∈ F.attach, ∀ w ∈ F.attach,
      (⟨v.1, hF v.2⟩ : S) = ⟨w.1, hF w.2⟩ → v = w := by
    rintro ⟨v, hv⟩ - ⟨w, hw⟩ - h
    simpa [Subtype.ext_iff] using h
  calc ∑ v ∈ F, g v
      = ∑ w ∈ F', g w.1 := by
        rw [Finset.sum_image hinj, ← Finset.sum_attach F g]
    _ ≤ ∑ w ∈ F', nsgWr K s w.1 := by
        refine Finset.sum_le_sum fun w _ => hgle w.1 w.2
    _ ≤ nsgTail K S s :=
        hsum.sum_le_tsum F' fun w _ => nsgWr_nonneg K s w.1

private lemma nsg_sum_le_master {F : Finset (Ideal (𝓞 K))} (hF : ∀ v ∈ F, v ≠ (0 : Ideal (𝓞 K)))
    {s : ℝ} (hs : 1 < s)
    {g : Ideal (𝓞 K) → ℝ} (_ : ∀ v, 0 ≤ g v) (hgle : ∀ v ∈ F, g v ≤ nsgWr K s v) :
    ∑ v ∈ F, g v ≤ ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWr K s I.1 := by
  classical
  have hsum := nsg_summable_master K hs
  let F' : Finset {I : Ideal (𝓞 K) // I ≠ 0} :=
    F.attach.image fun v => ⟨v.1, hF v.1 v.2⟩
  have hinj : ∀ v ∈ F.attach, ∀ w ∈ F.attach,
      (⟨v.1, hF v.1 v.2⟩ : {I : Ideal (𝓞 K) // I ≠ 0}) = ⟨w.1, hF w.1 w.2⟩ → v = w := by
    rintro ⟨v, hv⟩ - ⟨w, hw⟩ - h
    simpa [Subtype.ext_iff] using h
  calc ∑ v ∈ F, g v
      = ∑ w ∈ F', g w.1 := by
        rw [Finset.sum_image hinj, ← Finset.sum_attach F g]
    _ ≤ ∑ w ∈ F', nsgWr K s w.1 := by
        refine Finset.sum_le_sum fun w hw => ?_
        have : w.1 ∈ F := by
          have := Finset.mem_image.mp hw
          obtain ⟨v, hv, rfl⟩ := this
          exact v.2
        exact hgle w.1 this
    _ ≤ _ := hsum.sum_le_tsum F' fun w _ => nsgWr_nonneg K s w.1

private lemma nsg_supported_le_exp {S : Set (Ideal (𝓞 K))} (hS : S ⊆ nsgPrimes K)
    {s : ℝ} (hs : 1 < s) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, nsgWe K s A.1) ≤
      ENNReal.ofReal (Real.exp (nsgTail K S s + 2 * nsgZ2 K)) := by
  classical
  rw [tsum_memSupp_eq_iSup]
  refine iSup_le ?_
  rintro ⟨F, hFS⟩
  have hFprime : ∀ v ∈ (↑F : Set (Ideal (𝓞 K))), Prime v :=
    fun v hv => nsg_prime_of_mem_primes K (hS (hFS hv))
  have hmul : ∀ I J : Ideal (𝓞 K), I ≠ 0 → J ≠ 0 →
      nsgWe K s (I * J) = nsgWe K s I * nsgWe K s J :=
    fun I J hI hJ => nsgWe_mul K hI hJ s
  have hpeel := tsum_memSupp_peel_ennreal (nsgWe K s) hmul F
    (↑F : Set (Ideal (𝓞 K))) le_rfl hFprime
  rw [Set.diff_self] at hpeel
  rw [hpeel, tsum_memSupp_empty_ennreal, nsgWe, nsgWr_one, ENNReal.ofReal_one, mul_one]

  have hfac : ∀ v ∈ F, (∑' k : ℕ, nsgWe K s (v ^ k)) ≤
      ENNReal.ofReal (Real.exp (nsgWr K s v + 2 * nsgWr K s v ^ 2)) := by
    intro v hv
    have hvmax : (v : Ideal (𝓞 K)).IsMaximal := hS (hFS hv)
    rw [nsg_geom_ennreal K hvmax hs.le]
    exact ENNReal.ofReal_le_ofReal
      (nsg_one_sub_inv_le_exp (nsgWr_nonneg K s v) (nsgWr_le_half K hvmax hs.le))
  calc ∏ v ∈ F, (∑' k : ℕ, nsgWe K s (v ^ k))
      ≤ ∏ v ∈ F, ENNReal.ofReal (Real.exp (nsgWr K s v + 2 * nsgWr K s v ^ 2)) :=
        Finset.prod_le_prod' hfac
    _ = ENNReal.ofReal (∏ v ∈ F, Real.exp (nsgWr K s v + 2 * nsgWr K s v ^ 2)) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun v _ => (Real.exp_pos _).le]
    _ = ENNReal.ofReal (Real.exp (∑ v ∈ F, (nsgWr K s v + 2 * nsgWr K s v ^ 2))) := by
        rw [Real.exp_sum]
    _ ≤ ENNReal.ofReal (Real.exp (nsgTail K S s + 2 * nsgZ2 K)) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have h1 : ∑ v ∈ F, nsgWr K s v ≤ nsgTail K S s :=
          nsg_sum_le_tail K hS hFS hs (nsgWr_nonneg K s) (fun v _ => le_rfl)
        have h2 : ∑ v ∈ F, nsgWr K s v ^ 2 ≤ nsgZ2 K := by
          unfold nsgZ2
          refine nsg_sum_le_master K
            (fun v hv => nsg_maximal_ne_bot K (hS (hFS hv)))
            (by norm_num : (1:ℝ) < 2) (fun v => sq_nonneg _) ?_
          exact fun v hv => nsgWr_sq_le K (hS (hFS hv)) hs.le
        linarith
end NsgbALower

section NsgbAFinal

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal Filter"
p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors Topology"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

private noncomputable def nsgEquivNzd :
    {I : Ideal (𝓞 K) // MemSupp (nsgPrimes K) I} ≃ {I : Ideal (𝓞 K) // I ≠ 0} where
  toFun A := ⟨A.1, A.2.1⟩
  invFun I := ⟨I.1, nsg_memSupp_primes K I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma nsg_zeta_toReal (s : ℝ) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A}, nsgWe K s A.1).toReal =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWr K s I.1 := by
  have h0 : (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A}, nsgWe K s A.1) =
      ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A},
        ENNReal.ofReal (nsgWr K s A.1) :=
    tsum_congr fun A => rfl
  rw [h0, ENNReal.tsum_toReal_eq (fun A => ENNReal.ofReal_ne_top)]
  have h1 : ∀ A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A},
      (ENNReal.ofReal (nsgWr K s A.1)).toReal = nsgWr K s A.1 :=
    fun A => ENNReal.toReal_ofReal (nsgWr_nonneg K s A.1)
  rw [tsum_congr h1]
  have hre := (nsgEquivNzd K).tsum_eq
    (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => nsgWr K s I.1)
  rw [← hre]
  exact tsum_congr fun A => rfl

private lemma nsg_primes_ne_top {s : ℝ} (hs : 1 < s) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A}, nsgWe K s A.1) ≠ ⊤ :=
  (lt_of_le_of_lt (nsg_supported_le_exp K (fun _ hP => hP) hs)
    ENNReal.ofReal_lt_top).ne

omit [NumberField M] [IsGalois K M] in

private lemma nsg_A_ne_top {s : ℝ} (hs : 1 < s) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWe K s A.1) ≠ ⊤ :=
  (lt_of_le_of_lt (nsg_supported_le_exp K (nsgT1_subset_primes K M) hs)
    ENNReal.ofReal_lt_top).ne

private lemma nsg_A_lower (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q)
    (hdeg : Module.finrank K M = q) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      c * ((s - 1)⁻¹ ^ (1 - (q : ℝ)⁻¹)) ≤
        (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWe K s A.1).toReal := by
  obtain ⟨c₀, hc₀, hzeta⟩ := nsg_zeta_lower K
  obtain ⟨C₁, htail⟩ := nsg_tail_bound K M q hq h3q hdeg
  set K₁ : ℝ := Real.exp (C₁ + 2 * nsgZ2 K) with hK₁
  have hK₁pos : 0 < K₁ := Real.exp_pos _
  refine ⟨c₀ / K₁, div_pos hc₀ hK₁pos, ?_⟩
  filter_upwards [hzeta, htail, self_mem_nhdsWithin] with s hz ht hs1
  have hs1' : (1 : ℝ) < s := hs1
  have hu : (0 : ℝ) < (s - 1)⁻¹ := inv_pos.mpr (by linarith)

  have hsplit := tsum_memSupp_mul_ennreal (R := 𝓞 K) (nsgT1_disjoint_S1 K M)
    (nsgWe K s) (fun I J hI hJ => nsgWe_mul K hI.1 hJ.1 s)
  rw [nsgT1_union_S1] at hsplit

  have hB' := nsg_supported_le_exp K (S := nsgS1 K M) (fun P hP => hP.1) hs1'

  have hexp : Real.exp (nsgTail K (nsgS1 K M) s + 2 * nsgZ2 K) ≤
      K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹ := by
    have hsum : nsgTail K (nsgS1 K M) s + 2 * nsgZ2 K ≤
        (q : ℝ)⁻¹ * Real.log (s - 1)⁻¹ + (C₁ + 2 * nsgZ2 K) := by linarith
    calc Real.exp (nsgTail K (nsgS1 K M) s + 2 * nsgZ2 K)
        ≤ Real.exp ((q : ℝ)⁻¹ * Real.log (s - 1)⁻¹ + (C₁ + 2 * nsgZ2 K)) :=
          Real.exp_le_exp.mpr hsum
      _ = Real.exp ((q : ℝ)⁻¹ * Real.log (s - 1)⁻¹) * K₁ := by rw [Real.exp_add]
      _ = (s - 1)⁻¹ ^ (q : ℝ)⁻¹ * K₁ := by
          rw [Real.rpow_def_of_pos hu, mul_comm (Real.log _)]
      _ = K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹ := mul_comm _ _

  set Ae := ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWe K s A.1 with hAe
  have hAfin : Ae ≠ ⊤ := nsg_A_ne_top K M hs1'
  have hzeta_e : ENNReal.ofReal (c₀ * (s - 1)⁻¹) ≤ Ae *
      ENNReal.ofReal (K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹) := by
    calc ENNReal.ofReal (c₀ * (s - 1)⁻¹)
        ≤ ENNReal.ofReal (∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWr K s I.1) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_eq_mul_inv] at hz
          exact hz
      _ = ENNReal.ofReal ((∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A},
            nsgWe K s A.1).toReal) := by rw [nsg_zeta_toReal K]
      _ = ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A}, nsgWe K s A.1 :=
          ENNReal.ofReal_toReal (nsg_primes_ne_top K hs1')
      _ = Ae * ∑' B : {B : Ideal (𝓞 K) // MemSupp (nsgS1 K M) B}, nsgWe K s B.1 :=
          hsplit
      _ ≤ Ae * ENNReal.ofReal (Real.exp (nsgTail K (nsgS1 K M) s + 2 * nsgZ2 K)) :=
          mul_le_mul_right hB' Ae
      _ ≤ Ae * ENNReal.ofReal (K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hexp) Ae

  have hpos : 0 < K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹ :=
    mul_pos hK₁pos (Real.rpow_pos_of_pos hu _)
  have hAreal : c₀ * (s - 1)⁻¹ ≤ Ae.toReal * (K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹) := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hAfin ENNReal.ofReal_ne_top) hzeta_e
    rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hpos.le] at this

  have h0 : (s - 1)⁻¹ ^ ((q : ℝ))⁻¹ ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  have hdiv : c₀ * (s - 1)⁻¹ / (K₁ * (s - 1)⁻¹ ^ (q : ℝ)⁻¹) ≤ Ae.toReal :=
    (div_le_iff₀ hpos).mpr hAreal
  refine le_trans (le_of_eq ?_) hdiv
  rw [Real.rpow_sub hu, Real.rpow_one]
  field_simp

end NsgbAFinal

section NsgbBLower

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal Filter"
p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors Topology"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

private lemma nsgChi_pow (χ : ClassGroup (𝓞 K) →* ℂ) {v : Ideal (𝓞 K)} (hv : v ≠ 0)
    (k : ℕ) : nsgChi K χ (v ^ k) = nsgChi K χ v ^ k := by
  have hvk : v ^ k ≠ 0 := pow_ne_zero k hv
  have hsub : (⟨v ^ k, mem_nonZeroDivisors_of_ne_zero hvk⟩ : (Ideal (𝓞 K))⁰) =
      (⟨v, mem_nonZeroDivisors_of_ne_zero hv⟩ : (Ideal (𝓞 K))⁰) ^ k := rfl
  simp only [nsgChi, dif_pos hv, dif_pos hvk, hsub, _root_.map_pow]

private lemma nsgWc_pow (χ : ClassGroup (𝓞 K) →* ℂ) {v : Ideal (𝓞 K)} (hv : v ≠ 0)
    (s : ℝ) (k : ℕ) :
    nsgWc K χ s (v ^ k) = (nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ)) ^ k := by
  unfold nsgWc
  rw [nsgChi_pow K χ hv, nsgWr_pow, Complex.ofReal_pow, mul_pow]

private lemma nsgChi_norm_le (χ : ClassGroup (𝓞 K) →* ℂ)
    (hnorm : ∀ c, ‖χ c‖ = 1) (I : Ideal (𝓞 K)) : ‖nsgChi K χ I‖ ≤ 1 := by
  unfold nsgChi
  split
  · rw [hnorm]
  · simp

private lemma nsgWc_norm_le (χ : ClassGroup (𝓞 K) →* ℂ)
    (hnorm : ∀ c, ‖χ c‖ = 1) (s : ℝ) (I : Ideal (𝓞 K)) :
    ‖nsgWc K χ s I‖ ≤ nsgWr K s I := by
  unfold nsgWc
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (nsgWr_nonneg K s I)]
  calc ‖nsgChi K χ I‖ * nsgWr K s I ≤ 1 * nsgWr K s I :=
        mul_le_mul_of_nonneg_right (nsgChi_norm_le K χ hnorm I) (nsgWr_nonneg K s I)
    _ = nsgWr K s I := one_mul _

private lemma nsg_summable_wc_norm (χ : ClassGroup (𝓞 K) →* ℂ)
    (hnorm : ∀ c, ‖χ c‖ = 1) {S : Set (Ideal (𝓞 K))} (_ : S ⊆ nsgPrimes K)
    {s : ℝ} (hs : 1 < s) :
    Summable fun B : {B : Ideal (𝓞 K) // MemSupp S B} => ‖nsgWc K χ s B.1‖ := by
  have hmaster := nsg_summable_master K hs
  have hinj : Function.Injective
      (fun B : {B : Ideal (𝓞 K) // MemSupp S B} =>
        (⟨B.1, B.2.1⟩ : {I : Ideal (𝓞 K) // I ≠ 0})) := by
    rintro ⟨B, hB⟩ ⟨C, hC⟩ h
    simpa [Subtype.ext_iff] using h
  have hbig : Summable fun B : {B : Ideal (𝓞 K) // MemSupp S B} => nsgWr K s B.1 := by
    have := hmaster.comp_injective hinj
    simpa only [Function.comp_def] using this
  exact Summable.of_nonneg_of_le (fun B => norm_nonneg _)
    (fun B => nsgWc_norm_le K χ hnorm s B.1) hbig

private lemma nsg_supported_le_exp_tail {S : Set (Ideal (𝓞 K))} (hS : S ⊆ nsgPrimes K)
    {s : ℝ} (hs : 1 < s) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, nsgWe K s A.1) ≤
      ENNReal.ofReal (Real.exp (3 * nsgTail K S s)) := by
  classical
  rw [tsum_memSupp_eq_iSup]
  refine iSup_le ?_
  rintro ⟨F, hFS⟩
  have hFprime : ∀ v ∈ (↑F : Set (Ideal (𝓞 K))), Prime v :=
    fun v hv => nsg_prime_of_mem_primes K (hS (hFS hv))
  have hmul : ∀ I J : Ideal (𝓞 K), I ≠ 0 → J ≠ 0 →
      nsgWe K s (I * J) = nsgWe K s I * nsgWe K s J :=
    fun I J hI hJ => nsgWe_mul K hI hJ s
  have hpeel := tsum_memSupp_peel_ennreal (nsgWe K s) hmul F
    (↑F : Set (Ideal (𝓞 K))) le_rfl hFprime
  rw [Set.diff_self] at hpeel
  rw [hpeel, tsum_memSupp_empty_ennreal, nsgWe, nsgWr_one, ENNReal.ofReal_one, mul_one]
  have hfac : ∀ v ∈ F, (∑' k : ℕ, nsgWe K s (v ^ k)) ≤
      ENNReal.ofReal (Real.exp (3 * nsgWr K s v)) := by
    intro v hv
    have hvmax : (v : Ideal (𝓞 K)).IsMaximal := hS (hFS hv)
    rw [nsg_geom_ennreal K hvmax hs.le]
    refine ENNReal.ofReal_le_ofReal (le_trans
      (nsg_one_sub_inv_le_exp (nsgWr_nonneg K s v) (nsgWr_le_half K hvmax hs.le)) ?_)
    refine Real.exp_le_exp.mpr ?_
    have hx1 : nsgWr K s v ≤ 1 := le_trans (nsgWr_le_half K hvmax hs.le) (by norm_num)
    nlinarith [nsgWr_nonneg K s v]
  calc ∏ v ∈ F, (∑' k : ℕ, nsgWe K s (v ^ k))
      ≤ ∏ v ∈ F, ENNReal.ofReal (Real.exp (3 * nsgWr K s v)) :=
        Finset.prod_le_prod' hfac
    _ = ENNReal.ofReal (∏ v ∈ F, Real.exp (3 * nsgWr K s v)) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun v _ => (Real.exp_pos _).le]
    _ = ENNReal.ofReal (Real.exp (∑ v ∈ F, 3 * nsgWr K s v)) := by rw [Real.exp_sum]
    _ ≤ ENNReal.ofReal (Real.exp (3 * nsgTail K S s)) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        rw [← Finset.mul_sum]
        have h1 : ∑ v ∈ F, nsgWr K s v ≤ nsgTail K S s :=
          nsg_sum_le_tail K hS hFS hs (nsgWr_nonneg K s) (fun v _ => le_rfl)
        linarith

private lemma nsg_supported_real_le_exp_tail {S : Set (Ideal (𝓞 K))}
    (hS : S ⊆ nsgPrimes K) {s : ℝ} (hs : 1 < s) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, nsgWr K s A.1) ≤
      Real.exp (3 * nsgTail K S s) := by
  have hle := nsg_supported_le_exp_tail K hS hs
  have h1 : (∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, nsgWe K s A.1).toReal =
      ∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, nsgWr K s A.1 := by
    have h0 : (∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, nsgWe K s A.1) =
        ∑' A : {A : Ideal (𝓞 K) // MemSupp S A}, ENNReal.ofReal (nsgWr K s A.1) :=
      tsum_congr fun A => rfl
    rw [h0, ENNReal.tsum_toReal_eq (fun A => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun A => ENNReal.toReal_ofReal (nsgWr_nonneg K s A.1)
  have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [h1, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hmono

end NsgbBLower

section NsgbFinalPieces

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal Filter"
p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors Topology"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

private def nsgGens : Set (ClassGroup (𝓞 K)) :=
  {c | ∃ (P : (Ideal (𝓞 K))⁰),
    (P : Ideal (𝓞 K)).IsMaximal ∧ (Ideal.absNorm (P : Ideal (𝓞 K))).Prime ∧
    ¬ IsSplitPrime K M P ∧ c = ClassGroup.mk0 P}

omit [NumberField M] [IsGalois K M] in
private lemma nsg_mk0_mem_closure_of_multiset (m : Multiset (Ideal (𝓞 K)))
    (hm : ∀ P ∈ m, P ∈ nsgT1 K M) (hprod : m.prod ≠ 0) :
    ClassGroup.mk0 ⟨m.prod, mem_nonZeroDivisors_of_ne_zero hprod⟩ ∈
      Subgroup.closure (nsgGens K M) := by
  induction m using Multiset.induction_on with
  | empty =>
    have h1 : (⟨(Multiset.prod 0 : Ideal (𝓞 K)),
        mem_nonZeroDivisors_of_ne_zero hprod⟩ : (Ideal (𝓞 K))⁰) = 1 := by
      ext
      simp
    rw [h1, _root_.map_one]
    exact Subgroup.one_mem _
  | cons P m ih =>
    have hP : P ∈ nsgT1 K M := hm P (Multiset.mem_cons_self P m)
    have hP0 : P ≠ 0 := nsg_maximal_ne_bot K hP.1
    have hm0 : m.prod ≠ 0 := by
      intro h
      rw [Multiset.prod_cons, h, mul_zero] at hprod
      exact hprod rfl
    have hsplit : (⟨(P ::ₘ m).prod, mem_nonZeroDivisors_of_ne_zero hprod⟩ :
        (Ideal (𝓞 K))⁰) =
        ⟨P, mem_nonZeroDivisors_of_ne_zero hP0⟩ *
          ⟨m.prod, mem_nonZeroDivisors_of_ne_zero hm0⟩ := by
      ext
      simp [Multiset.prod_cons]
    rw [hsplit, _root_.map_mul]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_)
      (ih (fun Q hQ => hm Q (Multiset.mem_cons_of_mem hQ)) hm0)
    exact ⟨⟨P, mem_nonZeroDivisors_of_ne_zero hP0⟩, hP.1, hP.2.1, hP.2.2, rfl⟩

omit [NumberField M] [IsGalois K M] in

private lemma nsg_mk0_mem_closure {I : Ideal (𝓞 K)} (hI : MemSupp (nsgT1 K M) I) :
    ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI.1⟩ ∈
      Subgroup.closure (nsgGens K M) := by
  have hprod : (normalizedFactors I).prod = I := by
    rw [prod_normalizedFactors_eq hI.1, normalize_eq]
  have hne : (normalizedFactors I).prod ≠ 0 := by rw [hprod]; exact hI.1
  have hsub : (⟨(normalizedFactors I).prod, mem_nonZeroDivisors_of_ne_zero hne⟩ :
      (Ideal (𝓞 K))⁰) = ⟨I, mem_nonZeroDivisors_of_ne_zero hI.1⟩ := Subtype.ext hprod
  rw [← hsub]
  exact nsg_mk0_mem_closure_of_multiset K M _ hI.2 hne

omit [NumberField M] [IsGalois K M] in

private lemma nsg_A_factor_real (χ : ClassGroup (𝓞 K) →* ℂ)
    (hχH : ∀ c ∈ Subgroup.closure (nsgGens K M), χ c = 1) (s : ℝ) :
    (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWc K χ s A.1) =
      (((∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWr K s A.1) : ℝ) : ℂ) := by
  have hpt : ∀ A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A},
      nsgWc K χ s A.1 = ((nsgWr K s A.1 : ℝ) : ℂ) := by
    intro A
    unfold nsgWc nsgChi
    rw [dif_pos A.2.1, hχH _ (nsg_mk0_mem_closure K M A.2), one_mul]
  rw [tsum_congr hpt]
  exact (Complex.ofReal_tsum
    (fun A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A} => nsgWr K s A.1)).symm

private lemma nsg_exp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have he : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have h4 : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by
    rw [hsq]; norm_num [he]
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h4

private lemma nsg_geom_factor_lower {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    Real.exp (-‖z‖) ≤ ‖(1 - z)⁻¹‖ := by
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) = z := by linear_combination h
    rw [← h1] at hz
    norm_num at hz
  rw [norm_inv]
  have hub : ‖(1 : ℂ) - z‖ ≤ 1 + ‖z‖ := le_trans (norm_sub_le _ _) (by simp)
  have hexp : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by
    have := Real.add_one_le_exp ‖z‖
    linarith
  calc Real.exp (-‖z‖) = (Real.exp ‖z‖)⁻¹ := Real.exp_neg _
    _ ≤ (1 + ‖z‖)⁻¹ := inv_anti₀ (by positivity) hexp
    _ ≤ ‖(1 : ℂ) - z‖⁻¹ := inv_anti₀ (norm_pos_iff.mpr hne) hub

private lemma nsg_geomchi_eval (χ : ClassGroup (𝓞 K) →* ℂ)
    (hnorm : ∀ c, ‖χ c‖ = 1) {v : Ideal (𝓞 K)} (hv : v.IsMaximal) {s : ℝ} (hs : 1 ≤ s) :
    (∑' k : ℕ, nsgWc K χ s (v ^ k)) =
      (1 - nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ))⁻¹ := by
  have hv0 : v ≠ 0 := nsg_maximal_ne_bot K hv
  have hz : ‖nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (nsgWr_nonneg K s v)]
    unfold nsgChi
    rw [dif_pos hv0, hnorm, one_mul]
    exact lt_of_le_of_lt (nsgWr_le_half K hv hs) (by norm_num)
  calc (∑' k : ℕ, nsgWc K χ s (v ^ k))
      = ∑' k : ℕ, (nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ)) ^ k :=
        tsum_congr fun k => nsgWc_pow K χ hv0 s k
    _ = _ := tsum_geometric_of_norm_lt_one hz

private lemma nsg_norm_z (χ : ClassGroup (𝓞 K) →* ℂ) (hnorm : ∀ c, ‖χ c‖ = 1)
    {v : Ideal (𝓞 K)} (hv : v ≠ 0) (s : ℝ) :
    ‖nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ)‖ = nsgWr K s v := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (nsgWr_nonneg K s v)]
  unfold nsgChi
  rw [dif_pos hv, hnorm, one_mul]

private def nsgComplEquiv (u : Finset (nsgS1 K M : Set (Ideal (𝓞 K)))) :
    (nsgS1 K M \ ↑(u.image Subtype.val) : Set (Ideal (𝓞 K))) ≃
      {w : (nsgS1 K M : Set (Ideal (𝓞 K))) // w ∉ u} where
  toFun v := ⟨⟨v.1, v.2.1⟩, fun hmem => v.2.2 (by
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨v.1, v.2.1⟩, hmem, rfl⟩)⟩
  invFun w := ⟨w.1.1, w.1.2, fun hmem => w.2 (by
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hmem
    obtain ⟨x, hxu, hxval⟩ := hmem
    exact (Subtype.ext hxval : x = w.1) ▸ hxu)⟩
  left_inv v := rfl
  right_inv w := rfl

set_option maxHeartbeats 3200000 in

private lemma nsg_B_lower (χ : ClassGroup (𝓞 K) →* ℂ) (hnorm : ∀ c, ‖χ c‖ = 1)
    (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q) (hdeg : Module.finrank K M = q) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      c₂ * ((s - 1) ^ (q : ℝ)⁻¹) ≤
        ‖∑' B : {B : Ideal (𝓞 K) // MemSupp (nsgS1 K M) B}, nsgWc K χ s B.1‖ := by
  obtain ⟨C₁, htail⟩ := nsg_tail_bound K M q hq h3q hdeg
  refine ⟨(2 - Real.exp (1 / 2 : ℝ)) * Real.exp (-C₁),
    mul_pos (by linarith [nsg_exp_half_lt_two]) (Real.exp_pos _), ?_⟩
  filter_upwards [htail, self_mem_nhdsWithin] with s ht hs1
  have hs1' : (1 : ℝ) < s := hs1
  have hS1P : nsgS1 K M ⊆ nsgPrimes K := fun P hP => hP.1

  have htendsto := tendsto_tsum_compl_atTop_zero
    (fun v : (nsgS1 K M : Set (Ideal (𝓞 K))) => nsgWr K s v.1)
  obtain ⟨u, hu⟩ := (htendsto.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))).exists
  set F : Finset (Ideal (𝓞 K)) := u.image Subtype.val with hF
  have hFS1 : ↑F ⊆ nsgS1 K M := by
    intro P hP
    simp only [hF, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hP
    obtain ⟨w, _, rfl⟩ := hP
    exact w.2

  have htail_small : nsgTail K (nsgS1 K M \ ↑F) s ≤ 1 / 6 := by
    unfold nsgTail
    calc (∑' v : (nsgS1 K M \ ↑F : Set (Ideal (𝓞 K))), nsgWr K s v.1)
        = ∑' w : {w : (nsgS1 K M : Set (Ideal (𝓞 K))) // w ∉ u}, nsgWr K s w.1.1 := by
          rw [← (nsgComplEquiv K M u).tsum_eq
            (fun w : {w : (nsgS1 K M : Set (Ideal (𝓞 K))) // w ∉ u} =>
              nsgWr K s w.1.1)]
          exact tsum_congr fun v => rfl
      _ ≤ 1 / 6 := hu.le

  have hsummR : ∀ (S : Set (Ideal (𝓞 K))),
      Summable fun A : {A : Ideal (𝓞 K) // MemSupp S A} => nsgWr K s A.1 := by
    intro S
    have hinj : Function.Injective
        (fun A : {A : Ideal (𝓞 K) // MemSupp S A} =>
          (⟨A.1, A.2.1⟩ : {I : Ideal (𝓞 K) // I ≠ 0})) := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ h
      simpa [Subtype.ext_iff] using h
    exact ((nsg_summable_master K hs1').comp_injective hinj).congr fun A => rfl

  have hSprime : ∀ v ∈ nsgS1 K M, Prime v :=
    fun v hv => nsg_prime_of_mem_primes K (hS1P hv)
  have hsumS1n : Summable fun B : {B : Ideal (𝓞 K) // MemSupp (nsgS1 K M) B} =>
      ‖nsgWc K χ s B.1‖ := nsg_summable_wc_norm K χ hnorm hS1P hs1'
  have hpeel := tsum_memSupp_peel_complex (nsgWc K χ s)
    (fun I J hI hJ => nsgWc_mul K χ hI hJ s) F (nsgS1 K M) hFS1 hSprime hsumS1n

  set T := ∑' B : {B : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) B}, nsgWc K χ s B.1
    with hTdef
  have hsub : nsgS1 K M \ ↑F ⊆ nsgPrimes K := fun P hP => hS1P hP.1
  have hTlow : 2 - Real.exp (1 / 2 : ℝ) ≤ ‖T‖ := by

    have hR2 : (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A},
        nsgWr K s A.1) ≤ Real.exp (1 / 2 : ℝ) := by
      refine le_trans (nsg_supported_real_le_exp_tail K hsub hs1')
        (Real.exp_le_exp.mpr ?_)
      linarith [htail_small]
    have hsumCn : Summable fun A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A} =>
        ‖nsgWc K χ s A.1‖ := nsg_summable_wc_norm K χ hnorm hsub hs1'
    have hsumC : Summable fun A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A} =>
        nsgWc K χ s A.1 := hsumCn.of_norm
    set e1 : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A} :=
      ⟨1, memSupp_one _⟩ with he1
    have hsplit1 := hsumC.tsum_eq_add_tsum_ite e1
    have hWc1 : nsgWc K χ s e1.1 = 1 := nsgWc_one K χ s

    have hrest : ‖∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A},
        ite (A = e1) 0 (nsgWc K χ s A.1)‖ ≤ Real.exp (1 / 2 : ℝ) - 1 := by
      have hsum_iten : Summable fun A : {A : Ideal (𝓞 K) //
          MemSupp (nsgS1 K M \ ↑F) A} => ‖ite (A = e1) 0 (nsgWc K χ s A.1)‖ := by
        refine Summable.of_nonneg_of_le (fun A => norm_nonneg _) (fun A => ?_) hsumCn
        by_cases h : A = e1 <;> simp [h, norm_nonneg]
      refine le_trans (norm_tsum_le_tsum_norm hsum_iten) ?_
      have hsum_iter : Summable fun A : {A : Ideal (𝓞 K) //
          MemSupp (nsgS1 K M \ ↑F) A} => ite (A = e1) 0 (nsgWr K s A.1) := by
        refine Summable.of_nonneg_of_le (fun A => ?_) (fun A => ?_) (hsummR _)
        · by_cases h : A = e1 <;> simp [h, nsgWr_nonneg]
        · by_cases h : A = e1 <;> simp [h, nsgWr_nonneg]
      have hptle : ∀ A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A},
          ‖ite (A = e1) 0 (nsgWc K χ s A.1)‖ ≤ ite (A = e1) 0 (nsgWr K s A.1) := by
        intro A
        by_cases h : A = e1
        · simp [h]
        · simpa [h] using nsgWc_norm_le K χ hnorm s A.1
      refine le_trans (hsum_iten.tsum_le_tsum hptle hsum_iter) ?_

      have hsplitR := (hsummR (nsgS1 K M \ ↑F)).tsum_eq_add_tsum_ite e1
      have hWr1 : nsgWr K s e1.1 = 1 := nsgWr_one K s
      have : (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A},
          ite (A = e1) 0 (nsgWr K s A.1)) =
          (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A},
            nsgWr K s A.1) - 1 := by
        rw [hsplitR, hWr1]
        ring
      rw [this]
      linarith [hR2]

    rw [hTdef, hsplit1, hWc1]
    have := norm_sub_norm_le (1 : ℂ)
      (-(∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgS1 K M \ ↑F) A},
        ite (A = e1) 0 (nsgWc K χ s A.1)))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith [hrest, this]

  have hprod_low : Real.exp (-(nsgTail K (nsgS1 K M) s)) ≤
      ‖∏ v ∈ F, ∑' k : ℕ, nsgWc K χ s (v ^ k)‖ := by
    have hfac_eval : ∀ v ∈ F, (∑' k : ℕ, nsgWc K χ s (v ^ k)) =
        (1 - nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ))⁻¹ :=
      fun v hv => nsg_geomchi_eval K χ hnorm (hFS1 hv).1 hs1'.le
    rw [Finset.prod_congr rfl hfac_eval, norm_prod]
    have hfac_low : ∀ v ∈ F, Real.exp (-(nsgWr K s v)) ≤
        ‖(1 - nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ))⁻¹‖ := by
      intro v hv
      have hv0 : v ≠ 0 := nsg_maximal_ne_bot K (hFS1 hv).1
      have hzn := nsg_norm_z K χ hnorm hv0 s
      have hhalf : ‖nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ)‖ ≤ 1 / 2 := by
        rw [hzn]
        exact nsgWr_le_half K (hFS1 hv).1 hs1'.le
      have hg := nsg_geom_factor_lower hhalf
      rwa [hzn] at hg
    calc Real.exp (-(nsgTail K (nsgS1 K M) s))
        ≤ Real.exp (-(∑ v ∈ F, nsgWr K s v)) := by
          refine Real.exp_le_exp.mpr (neg_le_neg ?_)
          exact nsg_sum_le_tail K hS1P hFS1 hs1' (nsgWr_nonneg K s) (fun v _ => le_rfl)
      _ = ∏ v ∈ F, Real.exp (-(nsgWr K s v)) := by
          rw [← Real.exp_sum]
          congr 1
          simp
      _ ≤ ∏ v ∈ F, ‖(1 - nsgChi K χ v * ((nsgWr K s v : ℝ) : ℂ))⁻¹‖ :=
          Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) hfac_low

  have hexp_tail : Real.exp (-C₁) * (s - 1) ^ (q : ℝ)⁻¹ ≤
      Real.exp (-(nsgTail K (nsgS1 K M) s)) := by
    have h2 : Real.exp (-((q : ℝ)⁻¹ * Real.log (s - 1)⁻¹ + C₁)) ≤
        Real.exp (-(nsgTail K (nsgS1 K M) s)) :=
      Real.exp_le_exp.mpr (neg_le_neg ht)
    refine le_trans (le_of_eq ?_) h2
    rw [neg_add, Real.exp_add, mul_comm (Real.exp _)]
    congr 1
    rw [Real.log_inv, mul_neg, neg_neg, ← Real.log_rpow (by linarith : (0:ℝ) < s - 1),
      Real.exp_log (Real.rpow_pos_of_pos (by linarith) _)]

  rw [hpeel, norm_mul]
  calc (2 - Real.exp (1 / 2 : ℝ)) * Real.exp (-C₁) * (s - 1) ^ (q : ℝ)⁻¹
      = (Real.exp (-C₁) * (s - 1) ^ (q : ℝ)⁻¹) * (2 - Real.exp (1 / 2 : ℝ)) := by ring
    _ ≤ Real.exp (-(nsgTail K (nsgS1 K M) s)) * (2 - Real.exp (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hexp_tail ?_
        linarith [nsg_exp_half_lt_two]
    _ ≤ ‖∏ v ∈ F, ∑' k : ℕ, nsgWc K χ s (v ^ k)‖ * ‖T‖ := by
        refine mul_le_mul hprod_low hTlow (by linarith [nsg_exp_half_lt_two])
          (norm_nonneg _)

end NsgbFinalPieces

end SplicePart5

section SplicePart6

section NsgbSolutionAux1

p2m_open "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField Ideal NumberField.Ideal Filter"
p2m_open_scoped "NumberField P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.NumberField nonZeroDivisors Topology"

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

theorem solution (q : ℕ) (hq : q.Prime) (h3q : 3 ≤ q) (hdeg : Module.finrank K M = q) :
    (⊤ : Subgroup (ClassGroup (𝓞 K))) =
      Subgroup.closure {c | ∃ (P : (Ideal (𝓞 K))⁰),
        (P : Ideal (𝓞 K)).IsMaximal ∧ (Ideal.absNorm (P : Ideal (𝓞 K))).Prime ∧
        ¬ IsSplitPrime K M P ∧ c = ClassGroup.mk0 P} := by
  change (⊤ : Subgroup (ClassGroup (𝓞 K))) = Subgroup.closure (nsgGens K M)
  by_contra hne
  have hH : Subgroup.closure (nsgGens K M) ≠ ⊤ := fun h ↦ hne h.symm

  obtain ⟨χ, hχ1, hχH, hnorm⟩ := nsg_exists_char K (Subgroup.closure (nsgGens K M)) hH

  obtain ⟨B, hB⟩ := nsg_chiL_bound K χ hχ1 hnorm

  obtain ⟨c₁, hc₁, hA⟩ := nsg_A_lower K M q hq h3q hdeg
  obtain ⟨c₂, hc₂, hBl⟩ := nsg_B_lower K M χ hnorm q hq h3q hdeg
  refine nsg_endgame_rpow (a := 1 - 2 * (q : ℝ)⁻¹) (c := c₁ * c₂) (B := B)
    (g := fun s ↦ ‖∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWc K χ s I.1‖)
    (nsg_exp_pos h3q) (mul_pos hc₁ hc₂) ?_ ?_
  ·
    filter_upwards [hA, hBl, self_mem_nhdsWithin] with s hAs hBs hs1
    have hs1' : (1 : ℝ) < s := hs1
    have hT1P : nsgT1 K M ⊆ nsgPrimes K := nsgT1_subset_primes K M
    have hS1P : nsgS1 K M ⊆ nsgPrimes K := fun P hP ↦ hP.1

    have hsplit := tsum_memSupp_mul_complex (R := 𝓞 K) (nsgT1_disjoint_S1 K M) (nsgWc K χ s)
      (fun I J hI hJ ↦ nsgWc_mul K χ hI.1 hJ.1 s)
      (nsg_summable_wc_norm K χ hnorm hT1P hs1') (nsg_summable_wc_norm K χ hnorm hS1P hs1')
    rw [nsgT1_union_S1] at hsplit
    have hL : ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWc K χ s I.1 =
        ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgPrimes K) A}, nsgWc K χ s A.1 := by
      rw [← (nsgEquivNzd K).tsum_eq (fun I : {I : Ideal (𝓞 K) // I ≠ 0} ↦ nsgWc K χ s I.1)]
      exact tsum_congr fun A ↦ rfl

    have hAreal := nsg_A_factor_real K M χ hχH s
    have hA_toReal : (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWe K s A.1).toReal =
        ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWr K s A.1 := by
      have h0 : (∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWe K s A.1) =
          ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, ENNReal.ofReal (nsgWr K s A.1) :=
        tsum_congr fun A ↦ rfl
      rw [h0, ENNReal.tsum_toReal_eq (fun A ↦ ENNReal.ofReal_ne_top)]
      exact tsum_congr fun A ↦ ENNReal.toReal_ofReal (nsgWr_nonneg K s A.1)
    have hA0 : 0 ≤ ∑' A : {A : Ideal (𝓞 K) // MemSupp (nsgT1 K M) A}, nsgWr K s A.1 :=
      tsum_nonneg fun A ↦ nsgWr_nonneg K s A.1
    show c₁ * c₂ * (s - 1)⁻¹ ^ (1 - 2 * (q : ℝ)⁻¹) ≤
      ‖∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWc K χ s I.1‖
    rw [hL, hsplit, norm_mul, hAreal, Complex.norm_real, Real.norm_of_nonneg hA0, ← hA_toReal,
      ← nsg_rpow_combine hs1' ((q : ℝ)⁻¹)]
    calc c₁ * c₂ * ((s - 1)⁻¹ ^ (1 - (q : ℝ)⁻¹) * (s - 1) ^ (q : ℝ)⁻¹)
        = (c₁ * ((s - 1)⁻¹ ^ (1 - (q : ℝ)⁻¹))) * (c₂ * ((s - 1) ^ (q : ℝ)⁻¹)) := by ring
      _ ≤ _ := mul_le_mul hAs hBs (mul_nonneg hc₂.le (Real.rpow_nonneg (by linarith) _))
          ENNReal.toReal_nonneg
  ·
    filter_upwards [Ioo_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with s hs
    show ‖∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, nsgWc K χ s I.1‖ ≤ B
    rw [nsg_L_aux4_eq_aux2 K χ s]
    exact hB s hs

end NsgbSolutionAux1

end SplicePart6

end S_NumberField_classGroup_eq_closure_nonSplit_degOne
end P2MW
export P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne (solution)
