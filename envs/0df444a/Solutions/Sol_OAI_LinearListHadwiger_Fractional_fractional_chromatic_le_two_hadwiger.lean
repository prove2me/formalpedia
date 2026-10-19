-- Prove2me | solution 1 for OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:47:56.397775+00:00
-- url     : https://prove2.me/submissions/1875d33d-234a-4cea-8ea0-0123d98e264d

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000
import Theorems.Thm_OAI_LinearListHadwiger_Fractional_dual_weight_le_two_hadwiger

section
-- module Solutions.OAIQW_ListHadwiger.Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

lemma Stable.mono {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {I J : Finset V} (h : Stable G I) (hJI : J ⊆ I) :
    Stable G J := fun v hv w hw => h v (hJI hv) w (hJI hw)

lemma cost_nonneg {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) : 0 ≤ cost μ :=
  Finset.sum_nonneg (fun I _ => h.1 I)

lemma singletonWeights_cover (G : SimpleGraph V) : Cover G singletonWeights := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro I
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> norm_num
  · intro I hn
    apply Finset.sum_eq_zero
    intro v _
    rw [ite_eq_right]
    rintro rfl
    exact hn (stable_singleton G v)
  · intro v
    have hpos (I : Finset V) : 0 ≤ (if v ∈ I then singletonWeights I else 0) := by
      split_ifs
      · exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
      · exact le_rfl
    have h := Finset.single_le_sum (fun I _ => hpos I) (Finset.mem_univ ({v} : Finset V))
    have hm : singletonWeights ({v} : Finset V) = 1 := by
      simp [singletonWeights,Finset.singleton_inj]
    simpa [hm] using h

lemma costs_nonempty (G : SimpleGraph V) :
    ({c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} : Set ℝ).Nonempty :=
  ⟨_,singletonWeights,singletonWeights_cover G,rfl⟩

lemma costs_bddBelow (G : SimpleGraph V) :
    BddBelow {c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} := by
  refine ⟨0,?_⟩
  rintro c ⟨μ,hμ,rfl⟩
  exact cost_nonneg hμ

lemma number_le_cost {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    number G ≤ cost μ := csInf_le (costs_bddBelow G) ⟨μ,h,rfl⟩

lemma Cover.clamp {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    Cover G (fun I => min (μ I) 1) := by
  classical
  refine ⟨fun I => le_min (h.1 I) zero_le_one,?_,?_⟩
  · intro I hn
    change min (μ I) 1 = 0
    rw [h.2.1 I hn]
    norm_num
  · intro v
    by_cases hall : ∀ I, v ∈ I → μ I ≤ 1
    · have heq : (∑ I, if v ∈ I then min (μ I) 1 else 0) =
          ∑ I, if v ∈ I then μ I else 0 := by
        apply Finset.sum_congr rfl
        intro I _
        split_ifs with hv
        · rw [min_eq_left (hall I hv)]
        · rfl
      rw [heq]
      exact h.2.2 v
    · push Not at hall
      obtain ⟨I,hv,hI⟩ := hall
      have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Finset V)))
        (f := fun J => if v ∈ J then min (μ J) 1 else 0)
        (fun J _ => by split_ifs; exact le_min (h.1 J) zero_le_one; exact le_rfl)
        (Finset.mem_univ I)
      simpa only [ite_eq_left hv,min_eq_right (le_of_lt hI)] using hs

lemma cover_isClosed (G : SimpleGraph V) : IsClosed {μ : Finset V → ℝ | Cover G μ} := by
  change IsClosed ({μ : Finset V → ℝ | ∀ I, 0 ≤ μ I} ∩
    ({μ | ∀ I, ¬Stable G I → μ I = 0} ∩
     {μ | ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0}))
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun I => isClosed_le continuous_const (continuous_apply I)
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases h : Stable G I
    · simp only [h,not_true_eq_false,false_implies,Set.ofPred_true]
      exact isClosed_univ
    · simp only [h,not_false_eq_true,true_implies]
      exact isClosed_eq (continuous_apply I) continuous_const
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    apply continuous_finsetSum
    intro I _
    by_cases hv : v ∈ I
    · simpa only [ite_eq_left hv] using continuous_apply I
    · simp only [ite_eq_right hv]
      exact continuous_const

lemma cost_continuous {V : Type} [Fintype V] [DecidableEq V] : Continuous (cost (V := V)) := by
  apply continuous_finsetSum
  intro I _
  exact continuous_apply I

theorem optimum_exists (G : SimpleGraph V) : ∃ μ, Cover G μ ∧ cost μ = number G := by
  classical
  let K : Set ((Finset V) → ℝ) := Set.Icc 0 1 ∩ {μ | Cover G μ}
  have hcomp : IsCompact K := isCompact_Icc.inter_right (cover_isClosed G)
  have hne : K.Nonempty := by
    refine ⟨fun I => min (singletonWeights I) 1,⟨?_,?_⟩,(singletonWeights_cover G).clamp⟩
    · intro I
      exact le_min ((singletonWeights_cover G).1 I) zero_le_one
    · intro I
      exact min_le_right _ _
  obtain ⟨μ,hμ,hmin⟩ := hcomp.exists_isMinOn hne cost_continuous.continuousOn
  refine ⟨μ,hμ.2,le_antisymm ?_ (number_le_cost hμ.2)⟩
  apply le_csInf (costs_nonempty G)
  rintro c ⟨ν,hν,rfl⟩
  apply (hmin (show (fun I => min (ν I) 1) ∈ K from ?_)).trans
    (Finset.sum_le_sum (fun I _ => min_le_left (ν I) 1))
  exact ⟨⟨fun I => le_min (hν.1 I) zero_le_one,fun I => min_le_right _ _⟩,hν.clamp⟩

lemma Dual.le_one {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (v : V) : w v ≤ 1 := by
  simpa using hw.2 {v} (stable_singleton G v)

lemma dual_zero {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Dual G (fun _ => 0) := by
  simp [Dual]

lemma dual_isClosed {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : IsClosed {w : V → ℝ | Dual G w} := by
  classical
  change IsClosed ({w : V → ℝ | ∀ v, 0 ≤ w v} ∩
    {w | ∀ I, Stable G I → ∑ v ∈ I, w v ≤ 1})
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases hI : Stable G I
    · simp only [hI,true_implies]
      apply isClosed_le _ continuous_const
      exact continuous_finsetSum I (fun v _ => continuous_apply v)
    · simp only [hI,false_implies,Set.ofPred_true]
      exact isClosed_univ

lemma dual_maximum (G : SimpleGraph V) :
    ∃ w, Dual G w ∧ ∀ z, Dual G z → ∑ v, z v ≤ ∑ v, w v := by
  classical
  have hc : IsCompact {w : V → ℝ | Dual G w} :=
    isCompact_Icc.of_isClosed_subset (dual_isClosed G) (by
      intro w hw
      exact ⟨hw.1,hw.le_one⟩)
  exact hc.exists_isMaxOn ⟨_,dual_zero G⟩
    (continuous_finsetSum Finset.univ (fun v _ => continuous_apply v)).continuousOn

lemma weak_duality {G : SimpleGraph V} {μ : Finset V → ℝ} {w : V → ℝ}
    (hμ : Cover G μ) (hw : Dual G w) : ∑ v, w v ≤ cost μ := by
  classical
  calc
    ∑ v, w v ≤ ∑ v, w v * ∑ I, if v ∈ I then μ I else 0 := by
      apply Finset.sum_le_sum
      intro v _
      simpa using mul_le_mul_of_nonneg_left (hμ.2.2 v) (hw.1 v)
    _ = ∑ I, μ I * ∑ v ∈ I, w v := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I _
      simp only [mul_ite,mul_zero,mul_comm (w _) (μ I),← Finset.mul_sum]
      simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
      rw [Finset.mul_sum]
    _ ≤ cost μ := by
      apply Finset.sum_le_sum
      intro I _
      by_cases hI : Stable G I
      · simpa using mul_le_mul_of_nonneg_left (hw.2 I hI) (hμ.1 I)
      · simp [hμ.2.1 I hI]

lemma dual_le_number {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) :
    ∑ v, w v ≤ number G := by
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  rw [← heq]
  exact weak_duality hμ hw

lemma constant_mem_hull_cover (G : SimpleGraph V) {r : ℝ} (hr : 0 < r)
    (hx : (fun _ : V => 1 / r) ∈ convexHull ℝ {x | ∃ I, Stable G I ∧ indicator I = x}) :
    ∃ μ, Cover G μ ∧ cost μ = r := by
  classical
  obtain ⟨ι,hi,w,z,hw,hws,hz,hx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  choose I hI heq using hz
  let μ : Finset V → ℝ := fun J => ∑ i, if I i = J then r * w i else 0
  have hmass : cost μ = r := by
    unfold cost μ
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum,hws,mul_one]
  refine ⟨μ,⟨?_,?_,?_⟩,hmass⟩
  · intro J
    exact Finset.sum_nonneg fun i _ => by split_ifs; exact mul_nonneg hr.le (hw i); exact le_rfl
  · intro J hn
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro he
    exact hn (he ▸ hI i)
  · intro v
    have hxv := congrFun hx v
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hxv
    have hzv (i : ι) : z i v = if v ∈ I i then 1 else 0 := congrFun (heq i).symm v
    simp only [hzv,mul_ite,mul_one,mul_zero] at hxv
    have hm : (∑ J, if v ∈ J then μ J else 0) = r * ∑ i, if v ∈ I i then w i else 0 := by
      have hdis (J : Finset V) : (if v ∈ J then μ J else 0) =
          ∑ i, if v ∈ J then (if I i = J then r * w i else 0) else 0 := by
        by_cases h : v ∈ J <;> simp [h,μ]
      simp only [hdis]
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have heq : (fun J : Finset V => if v ∈ J then if I i = J then r * w i else 0 else 0) =
          (fun J => if I i = J then (if v ∈ I i then r * w i else 0) else 0) := by
        funext J
        by_cases hh : I i = J
        · subst J; simp
        · simp [hh]
      rw [heq]
      simp [mul_ite]
    rw [hm,hxv]
    exact le_of_eq (by field_simp)

lemma functional_eq_sum (f : StrongDual ℝ (V → ℝ)) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have hx : x = ∑ v, x v • Pi.single v 1 := by
    ext u
    simp [Pi.single_apply,smul_eq_mul,Finset.sum_apply]
  conv_lhs => rw [hx]
  simp

lemma functional_indicator (f : StrongDual ℝ (V → ℝ)) (I : Finset V) :
    f (indicator I) = ∑ v ∈ I, f (Pi.single v 1) := by
  classical
  rw [functional_eq_sum]
  simp only [indicator,ite_mul,one_mul,zero_mul,← Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter]

lemma dual_above (G : SimpleGraph V) {r : ℝ} (hr : 0 < r) (hrn : r < number G) :
    ∃ w, Dual G w ∧ r < ∑ v, w v := by
  classical
  let S : Set (V → ℝ) := {x | ∃ I, Stable G I ∧ indicator I = x}
  have hfin : S.Finite := (Set.finite_range (indicator (V := V))).subset (by
    rintro x ⟨I,hI,rfl⟩; exact ⟨I,rfl⟩)
  have hn : (fun _ : V => 1/r) ∉ convexHull ℝ S := by
    intro hx
    obtain ⟨μ,hμ,hm⟩ := constant_mem_hull_cover G hr hx
    have hh := number_le_cost hμ
    linarith
  obtain ⟨f,u,hf,hu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ S) (hfin.isClosed_convexHull ℝ) hn
  have hi (I : Finset V) (hI : Stable G I) :
      ∑ v ∈ I, f (Pi.single v 1) < u := by
    rw [← functional_indicator]
    exact hf _ (subset_convexHull ℝ S ⟨I,hI,rfl⟩)
  have hup : 0 < u := by simpa using hi ∅ (stable_empty G)
  let a : V → ℝ := fun v => f (Pi.single v 1)
  let w : V → ℝ := fun v => max (a v) 0 / u
  refine ⟨w,⟨fun v => div_nonneg (le_max_right _ _) hup.le,?_⟩,?_⟩
  · intro I hI
    have hm : (∑ v ∈ I, max (a v) 0) = ∑ v ∈ I.filter (fun v => 0 ≤ a v), a v := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : 0 ≤ a v
      · simp [hv]
      · simp [hv,max_eq_right (le_of_not_ge hv)]
    have hb := hi (I.filter (fun v => 0 ≤ a v))
      (hI.mono (Finset.filter_subset _ _))
    change ∑ v ∈ I, max (a v) 0 / u ≤ 1
    rw [← Finset.sum_div,div_le_one hup]
    rw [hm]
    exact hb.le
  · have hconst : f (fun _ : V => 1/r) = (∑ v, a v) / r := by
      rw [functional_eq_sum]
      simp only [← Finset.mul_sum,div_eq_mul_inv,mul_comm,mul_one,a]
    rw [hconst] at hu
    have hbig : r * u < ∑ v, a v := by
      have := (lt_div_iff₀ hr).mp hu
      nlinarith
    have hle : (∑ v, a v) ≤ ∑ v, max (a v) 0 :=
      Finset.sum_le_sum (fun v _ => le_max_left _ _)
    change r < ∑ v, max (a v) 0 / u
    rw [← Finset.sum_div,lt_div_iff₀ hup]
    exact hbig.trans_le hle

theorem duality (G : SimpleGraph V) :
    ∃ w, Dual G w ∧ ∑ v, w v = number G := by
  classical
  obtain ⟨w,hw,hm⟩ := dual_maximum G
  refine ⟨w,hw,le_antisymm (dual_le_number hw) ?_⟩
  by_contra hh
  have hh' : (∑ v, w v) < number G := lt_of_not_ge hh
  have hn : 0 ≤ ∑ v, w v := Finset.sum_nonneg (fun v _ => hw.1 v)
  let r := ((∑ v, w v) + number G) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrn : r < number G := by dsimp [r]; linarith
  obtain ⟨z,hz,hrz⟩ := dual_above G hr hrn
  have hzw := hm z hz
  dsimp [r] at hrz
  linarith

end LinearListHadwiger.Fractional

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace Fractional
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fractional_chromatic_le_two_hadwiger_oai (G : SimpleGraph V) :
    sInf {c : ℝ | ∃ μ : Finset V → ℝ,
      ((∀ I, 0 ≤ μ I) ∧ (∀ I, ¬(∀ v ∈ I, ∀ u ∈ I, ¬G.Adj v u) → μ I = 0) ∧
        ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0) ∧ ∑ I, μ I = c} ≤
      2 * (hadwigerNumber G : ℝ) := by
  change number G ≤ _
  obtain ⟨w,hw,he⟩ := duality G
  rw [← he]
  exact dual_weight_le_two_hadwiger G w hw.2

end Fractional

end LinearListHadwiger

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger_oai := @OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger_oai
