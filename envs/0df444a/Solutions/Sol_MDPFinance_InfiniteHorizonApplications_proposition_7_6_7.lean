-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.proposition_7_6_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:55:02.591133+00:00
-- url     : https://prove2.me/submissions/261bba43-6bd6-4bd2-9588-066c44585e50

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory


namespace MDPFinance.InfiniteHorizonApplications

section Gen
variable {β : ℝ} {q : ℕ × ℕ → ℝ}

lemma gk_PQ_le_add (hq : ∀ mn, 0 ≤ q mn ∧ q mn ≤ 1) (v w : ℕ × ℕ → ℝ) (c : ℝ)
    (h : ∀ mn, v mn ≤ w mn + c) (mn : ℕ × ℕ) : PQ q v mn ≤ PQ q w mn + c := by
  unfold PQ
  have h1 := h (mn.1+1, mn.2)
  have h2 := h (mn.1, mn.2+1)
  obtain ⟨a, b⟩ := hq mn
  nlinarith [mul_le_mul_of_nonneg_left h1 a, mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - q mn)]

lemma gk_PQ_const (c : ℝ) (mn : ℕ × ℕ) : PQ q (fun _ => c) mn = c := by
  unfold PQ; ring

lemma gk_PQ_add (v : ℕ × ℕ → ℝ) (c : ℝ) (mn : ℕ × ℕ) :
    PQ q (fun x => v x + c) mn = PQ q v mn + c := by
  unfold PQ; ring

lemma gk_PQ_lin (v w : ℕ × ℕ → ℝ) (a b : ℝ) (mn : ℕ × ℕ) :
    PQ q (fun x => a * v x + b * w x) mn = a * PQ q v mn + b * PQ q w mn := by
  unfold PQ; ring

lemma gk_comp (hβ0 : 0 < β) (hβ1 : β < 1) (hq : ∀ mn, 0 ≤ q mn ∧ q mn ≤ 1) (K K' : ℝ)
    (hK : K ≤ K') (v w : ℕ × ℕ → ℝ)
    (hv : ∀ mn, v mn ≤ max K (q mn + β * PQ q v mn))
    (hw : ∀ mn, max K' (q mn + β * PQ q w mn) ≤ w mn)
    (hb : ∃ C, ∀ mn, v mn - w mn ≤ C) : ∀ mn, v mn ≤ w mn := by
  obtain ⟨C, hC⟩ := hb
  have key : ∀ n : ℕ, ∀ mn, v mn ≤ w mn + β ^ n * max C 0 := by
    intro n
    induction n with
    | zero => intro mn; simp; linarith [hC mn, le_max_left C 0]
    | succ n ih =>
      intro mn
      have hP := gk_PQ_le_add hq v w _ ih mn
      have hP' := mul_le_mul_of_nonneg_left hP hβ0.le
      have e : β ^ (n+1) * max C 0 = β * (β ^ n * max C 0) := by ring
      calc v mn ≤ max K (q mn + β * PQ q v mn) := hv mn
        _ ≤ max K' (q mn + β * PQ q w mn) + β^(n+1) * max C 0 := by
          have hc : 0 ≤ β ^ (n+1) * max C 0 :=
            mul_nonneg (pow_nonneg hβ0.le _) (le_max_right _ _)
          apply max_le
          · have := le_max_left K' (q mn + β * PQ q w mn); linarith
          · have := le_max_right K' (q mn + β * PQ q w mn); rw [e]; linarith
        _ ≤ w mn + β ^ (n+1) * max C 0 := by linarith [hw mn]
  intro mn
  have ht : Filter.Tendsto (fun n : ℕ => w mn + β ^ n * max C 0) Filter.atTop
      (nhds (w mn + 0 * max C 0)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul
      tendsto_const_nhds)
  simp only [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun n => key n mn)

variable (KS : KStoppingValue β q)

lemma gk_bdd (K K' : ℝ) (c : ℝ) : ∃ C, ∀ mn, KS.J K mn - (KS.J K' mn + c) ≤ C := by
  obtain ⟨C1, h1⟩ := KS.hJ_bdd K
  obtain ⟨C2, h2⟩ := KS.hJ_bdd K'
  refine ⟨C1 + C2 + |c|, fun mn => ?_⟩
  have := h1 mn; have := h2 mn
  have := abs_le.1 (h1 mn); have := abs_le.1 (h2 mn); have := neg_abs_le c
  linarith

lemma gk_ge (K : ℝ) (mn : ℕ × ℕ) : K ≤ KS.J K mn := by
  rw [KS.hJ_fix]; exact le_max_left _ _

lemma gk_ge_A (K : ℝ) (mn : ℕ × ℕ) : q mn + β * PQ q (KS.J K) mn ≤ KS.J K mn := by
  rw [KS.hJ_fix K mn]; exact le_max_right _ _

lemma gk_mono {K K' : ℝ} (h : K ≤ K') (mn : ℕ × ℕ) : KS.J K mn ≤ KS.J K' mn := by
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq K K' h (KS.J K) (KS.J K') (fun x => (KS.hJ_fix K x).le)
    (fun x => (KS.hJ_fix K' x).ge) ?_ mn
  obtain ⟨C, hC⟩ := gk_bdd KS K K' 0
  exact ⟨C, fun x => by have := hC x; linarith⟩

lemma gk_sub {K K' : ℝ} (h : K ≤ K') (mn : ℕ × ℕ) : KS.J K' mn ≤ KS.J K mn + (K' - K) := by
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq K' K' le_rfl (KS.J K') (fun x => KS.J K x + (K' - K))
    (fun x => (KS.hJ_fix K' x).le) ?_ ?_ mn
  · intro x
    rw [gk_PQ_add]
    have h1 := gk_ge KS K x
    have h2 := gk_ge_A KS K x
    have hb := KS.hβ0; have hb1 := KS.hβ1
    apply max_le
    · linarith
    · nlinarith
  · obtain ⟨C, hC⟩ := gk_bdd KS K' K (K' - K)
    exact ⟨C, hC⟩

lemma gk_lip (K K' : ℝ) (mn : ℕ × ℕ) : |KS.J K mn - KS.J K' mn| ≤ |K - K'| := by
  rcases le_total K K' with h | h
  · have := gk_mono KS h mn; have := gk_sub KS h mn
    rw [abs_le, abs_of_nonpos (by linarith : K - K' ≤ 0)]; constructor <;> linarith
  · have := gk_mono KS h mn; have := gk_sub KS h mn
    rw [abs_le, abs_of_nonneg (by linarith : 0 ≤ K - K')]; constructor <;> linarith

lemma gk_cont (mn : ℕ × ℕ) : Continuous (KS.J · mn) := by
  have : LipschitzWith 1 (KS.J · mn) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact gk_lip KS x y mn
  exact this.continuous

lemma gk_convex (mn : ℕ × ℕ) : ConvexOn ℝ Set.univ (KS.J · mn) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq (a * x + b * y) (a * x + b * y) le_rfl
    (KS.J (a * x + b * y)) (fun z => a * KS.J x z + b * KS.J y z)
    (fun z => (KS.hJ_fix _ z).le) ?_ ?_ mn
  · intro z
    rw [gk_PQ_lin]
    have h1 := gk_ge KS x z
    have h2 := gk_ge_A KS x z
    have h3 := gk_ge KS y z
    have h4 := gk_ge_A KS y z
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb]
    · have e : q z + β * (a * PQ q (KS.J x) z + b * PQ q (KS.J y) z) =
          a * (q z + β * PQ q (KS.J x) z) + b * (q z + β * PQ q (KS.J y) z) := by
        have : q z = (a + b) * q z := by rw [hab, one_mul]
        linear_combination this
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]
  · obtain ⟨C1, h1⟩ := KS.hJ_bdd (a * x + b * y)
    obtain ⟨C2, h2⟩ := KS.hJ_bdd x
    obtain ⟨C3, h3⟩ := KS.hJ_bdd y
    refine ⟨C1 + a * C2 + b * C3, fun z => ?_⟩
    have := abs_le.1 (h1 z); have := abs_le.1 (h2 z); have := abs_le.1 (h3 z)
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (h2 z)).1 ha,
      mul_le_mul_of_nonneg_left (abs_le.1 (h3 z)).1 hb]

lemma gk_le_const (K : ℝ) (mn : ℕ × ℕ) : KS.J K mn ≤ max K (1 / (1 - β)) := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq K K le_rfl (KS.J K) (fun _ => max K (1 / (1 - β)))
    (fun x => (KS.hJ_fix K x).le) ?_ ?_ mn
  · intro z
    rw [gk_PQ_const]
    apply max_le (le_max_left _ _)
    have hq := (KS.hq z).2
    have h1 : 1 / (1 - β) ≤ max K (1 / (1 - β)) := le_max_right _ _
    have h2 : 1 ≤ (1 - β) * max K (1 / (1 - β)) := by
      rw [div_le_iff₀ (by linarith)] at h1; linarith
    nlinarith
  · obtain ⟨C, hC⟩ := KS.hJ_bdd K
    exact ⟨C - max K (1 / (1 - β)), fun z => by have := (abs_le.1 (hC z)).2; linarith⟩

lemma gk_sinf_mem (mn : ℕ × ℕ) : KS.J (GittinsIndex KS mn) mn = GittinsIndex KS mn := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  have hclosed : IsClosed {K : ℝ | KS.J K mn = K} := isClosed_eq (gk_cont KS mn) continuous_id
  have hne : ({K : ℝ | KS.J K mn = K}).Nonempty := by
    refine ⟨1 / (1 - β), le_antisymm ?_ (gk_ge KS _ _)⟩
    have := gk_le_const KS (1 / (1 - β)) mn
    rwa [max_self] at this
  have hbdd : BddBelow {K : ℝ | KS.J K mn = K} := by
    refine ⟨q mn / (1 - β), fun K hK => ?_⟩
    simp only [Set.mem_setOf_eq] at hK
    have h1 := gk_ge_A KS K mn
    have h2 := gk_PQ_le_add KS.hq (fun _ => K) (KS.J K) 0 (fun x => by simp [gk_ge KS K x]) mn
    rw [gk_PQ_const] at h2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact hclosed.csInf_mem hne hbdd

lemma gk_iff (K : ℝ) (mn : ℕ × ℕ) : KS.J K mn = K ↔ GittinsIndex KS mn ≤ K := by
  constructor
  · intro h
    show sInf {K : ℝ | KS.J K mn = K} ≤ K
    refine csInf_le ?_ (show K ∈ {K : ℝ | KS.J K mn = K} from h)
    refine ⟨q mn / (1 - β), fun K hK => ?_⟩
    have hb := KS.hβ0; have hb1 := KS.hβ1
    simp only [Set.mem_setOf_eq] at hK
    have h1 := gk_ge_A KS K mn
    have h2 := gk_PQ_le_add KS.hq (fun _ => K) (KS.J K) 0 (fun x => by simp [gk_ge KS K x]) mn
    rw [gk_PQ_const] at h2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro h
    have h1 := gk_sub KS h mn
    rw [gk_sinf_mem] at h1
    exact le_antisymm (by linarith) (gk_ge KS K mn)

lemma gk_lower (mn : ℕ × ℕ) : q mn / (1 - β) ≤ GittinsIndex KS mn := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  set K := GittinsIndex KS mn
  have hK := gk_sinf_mem KS mn
  have h1 := gk_ge_A KS K mn
  have h2 := gk_PQ_le_add KS.hq (fun _ => K) (KS.J K) 0 (fun x => by simp [gk_ge KS K x]) mn
  rw [gk_PQ_const] at h2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma gk_upper (mn : ℕ × ℕ) : GittinsIndex KS mn ≤ 1 / (1 - β) := by
  rw [← gk_iff]
  refine le_antisymm ?_ (gk_ge KS _ _)
  have := gk_le_const KS (1 / (1 - β)) mn
  rwa [max_self] at this

lemma gk_below (K : ℝ) (mn : ℕ × ℕ) (hK : K < GittinsIndex KS mn) :
    KS.J K mn = q mn + β * PQ q (KS.J K) mn := by
  have hne : KS.J K mn ≠ K := fun h => absurd ((gk_iff KS K mn).1 h) (not_le.2 hK)
  have := KS.hJ_fix K mn
  rcases le_total K (q mn + β * PQ q (KS.J K) mn) with h | h
  · rw [max_eq_right h] at this; exact this
  · rw [max_eq_left h] at this; exact absurd this hne

lemma gk_indiff (mn : ℕ × ℕ) :
    GittinsIndex KS mn = q mn + β * PQ q (KS.J (GittinsIndex KS mn)) mn := by
  set I := GittinsIndex KS mn with hI
  have hb := KS.hβ0
  have hmem := gk_sinf_mem KS mn
  rw [← hI] at hmem
  have hA := gk_ge_A KS I mn
  rw [hmem] at hA
  refine le_antisymm ?_ hA
  by_contra hlt
  push Not at hlt
  set D := I - (q mn + β * PQ q (KS.J I) mn)
  have hD : 0 < D := by simp only [D]; linarith
  have hK : I - D < I := by linarith
  have h1 := gk_below KS (I - D) mn hK
  have h2 : ∀ x, KS.J I x ≤ KS.J (I - D) x + D := by
    intro x; have := gk_sub KS hK.le x; linarith
  have h3 := gk_PQ_le_add KS.hq _ _ D h2 mn
  have h4 := gk_mono KS hK.le
  have h5 : PQ q (KS.J (I - D)) mn ≤ PQ q (KS.J I) mn := by
    have := gk_PQ_le_add KS.hq (KS.J (I - D)) (KS.J I) 0 (fun x => by simp [h4 x]) mn
    linarith
  have h6 := gk_sub KS hK.le mn
  rw [hmem] at h6
  -- J (I-D) mn ≥ I - D, and = q + β PQ(J(I-D)) ≤ q + β PQ(J I) = I - D
  have h7 : KS.J (I - D) mn ≤ q mn + β * PQ q (KS.J I) mn := by
    rw [h1]; nlinarith
  have h8 := gk_ge KS (I - D) mn
  -- so J(I-D) mn = I - D, contradiction with below
  have h9 : KS.J (I - D) mn = I - D := by
    apply le_antisymm _ h8; simp only [D] at h7 ⊢; linarith
  exact absurd ((gk_iff KS _ mn).1 h9) (not_le.2 hK)

end Gen

lemma gk_const_J {β p0 : ℝ} (KS : KStoppingValue β (fun _ => p0)) (K : ℝ) (mn : ℕ × ℕ) :
    KS.J K mn = max K (p0 / (1 - β)) := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  have hc : max K (p0 + β * max K (p0 / (1 - β))) = max K (p0 / (1 - β)) := by
    rcases le_total K (p0 / (1 - β)) with h | h
    · rw [max_eq_right h]
      have : p0 + β * (p0 / (1 - β)) = p0 / (1 - β) := by
        have : (1 - β) ≠ 0 := by linarith
        field_simp; ring
      rw [this, max_eq_right h]
    · rw [max_eq_left h]
      apply max_eq_left
      rw [div_le_iff₀ (by linarith)] at h
      nlinarith
  have hbd : ∃ C, ∀ x, KS.J K x - max K (p0 / (1 - β)) ≤ C := by
    obtain ⟨C, hC⟩ := KS.hJ_bdd K
    exact ⟨C - max K (p0 / (1 - β)), fun z => by have := (abs_le.1 (hC z)).2; linarith⟩
  have hbd' : ∃ C, ∀ x, max K (p0 / (1 - β)) - KS.J K x ≤ C := by
    obtain ⟨C, hC⟩ := KS.hJ_bdd K
    exact ⟨C + max K (p0 / (1 - β)), fun z => by have := (abs_le.1 (hC z)).1; linarith⟩
  apply le_antisymm
  · refine gk_comp KS.hβ0 KS.hβ1 KS.hq K K le_rfl (KS.J K) (fun _ => max K (p0 / (1 - β)))
      (fun x => (KS.hJ_fix K x).le) (fun x => ?_) hbd mn
    rw [gk_PQ_const, hc]
  · refine gk_comp KS.hβ0 KS.hβ1 KS.hq K K le_rfl (fun _ => max K (p0 / (1 - β))) (KS.J K)
      (fun x => ?_) (fun x => (KS.hJ_fix K x).ge) hbd' mn
    rw [gk_PQ_const, hc]

theorem cor768_core {β : ℝ} (KS : KStoppingValue β pMN) :
    (∀ K m n, KS.J K (m, n) = K ↔ GittinsIndex KS (m, n) ≤ K) ∧
      (∀ m n, GittinsIndex KS (m, n) = KS.J (GittinsIndex KS (m, n)) (m, n) ∧
        GittinsIndex KS (m, n) =
          pMN (m, n) + β * PMN (KS.J (GittinsIndex KS (m, n))) (m, n)) ∧
      (∀ m n, pMN (m, n) / (1 - β) ≤ GittinsIndex KS (m, n) ∧
        GittinsIndex KS (m, n) ≤ 1 / (1 - β)) ∧
      (∀ p0 : ℝ, ∀ KS' : KStoppingValue β (fun _ => p0), ∀ m n,
        GittinsIndex KS' (m, n) = p0 / (1 - β)) := by
  refine ⟨fun K m n => gk_iff KS K (m, n), fun m n => ⟨(gk_sinf_mem KS (m, n)).symm,
    gk_indiff KS (m, n)⟩, fun m n => ⟨gk_lower KS (m, n), gk_upper KS (m, n)⟩, ?_⟩
  intro p0 KS' m n
  have h1 := gk_sinf_mem KS' (m, n)
  rw [gk_const_J] at h1
  have h2 : KS'.J (p0 / (1 - β)) (m, n) = p0 / (1 - β) := by
    rw [gk_const_J, max_self]
  have h3 := (gk_iff KS' _ (m, n)).1 h2
  apply le_antisymm h3
  rw [← h1]; exact le_max_right _ _

theorem prop767_core {β : ℝ} (KS : KStoppingValue β pMN) (m n : ℕ) :
    (Monotone (KS.J · (m, n)) ∧ Continuous (KS.J · (m, n)) ∧ ConvexOn ℝ Set.univ (KS.J · (m, n))) ∧
      Antitone (fun K => KS.J K (m, n) - K) ∧
      ((∀ K, GittinsIndex KS (m, n) ≤ K → KS.J K (m, n) = K) ∧
        (∀ K, K < GittinsIndex KS (m, n) →
          KS.J K (m, n) = pMN (m, n) + β * PMN (KS.J K) (m, n)) ∧
        ∀ K, K ≤ KS.J K (m, n) ∧ KS.J K (m, n) ≤ max K (GittinsIndex KS (m, n))) ∧
      (∃ N : Set ℝ, MeasureTheory.volume N = 0 ∧
        (∀ K ∉ N, DifferentiableAt ℝ (KS.J · (m, n)) K) ∧
        (∀ K, DifferentiableWithinAt ℝ (KS.J · (m, n)) (Set.Ici K) K ∧
          DifferentiableWithinAt ℝ (KS.J · (m, n)) (Set.Iic K) K) ∧
        (∀ K, 0 ≤ derivWithin (KS.J · (m, n)) (Set.Ici K) K ∧
          derivWithin (KS.J · (m, n)) (Set.Ici K) K ≤ 1) ∧
        Monotone fun K => derivWithin (KS.J · (m, n)) (Set.Ici K) K) := by
  have hmono : Monotone (KS.J · (m, n)) := fun a b h => gk_mono KS h (m, n)
  have hconv := gk_convex KS (m, n)
  have hint : ∀ K : ℝ, K ∈ interior (Set.univ : Set ℝ) := by simp
  refine ⟨⟨hmono, gk_cont KS (m, n), hconv⟩, ?_, ⟨fun K h => (gk_iff KS K (m, n)).2 h,
    fun K h => gk_below KS K (m, n) h, fun K => ⟨gk_ge KS K (m, n), ?_⟩⟩, ?_⟩
  · intro a b h
    have := gk_sub KS h (m, n)
    simp only; linarith
  · rcases le_or_gt (GittinsIndex KS (m, n)) K with h | h
    · rw [(gk_iff KS K (m, n)).2 h]; exact le_max_left _ _
    · have := hmono h.le
      simp only at this
      rw [gk_sinf_mem] at this
      exact this.trans (le_max_right _ _)
  · refine ⟨{K | ¬ DifferentiableAt ℝ (KS.J · (m, n)) K}, ?_, ?_, ?_, ?_, ?_⟩
    · have := hmono.ae_differentiableAt
      rw [MeasureTheory.ae_iff] at this
      exact this
    · intro K hK
      simpa using hK
    · intro K
      exact ⟨(differentiableWithinAt_Ioi_iff_Ici).1 (hconv.differentiableWithinAt_Ioi_of_mem_interior (hint K)),
        (hconv.differentiableWithinAt_Iio_of_mem_interior (hint K)).hasDerivWithinAt.Iic_of_Iio.differentiableWithinAt⟩
    · intro K
      rw [← derivWithin_Ioi_eq_Ici, hconv.rightDeriv_eq_sInf_slope_of_mem_interior (hint K)]
      have hne : (slope (KS.J · (m, n)) K '' {y | y ∈ Set.univ ∧ K < y}).Nonempty :=
        ⟨_, ⟨K + 1, ⟨trivial, by linarith⟩, rfl⟩⟩
      have hs : ∀ y, K < y → 0 ≤ slope (KS.J · (m, n)) K y ∧ slope (KS.J · (m, n)) K y ≤ 1 := by
        intro y hy
        rw [slope_def_field]
        have h1 := gk_mono KS hy.le (m, n)
        have h2 := gk_sub KS hy.le (m, n)
        have hpos : 0 < y - K := by linarith
        constructor
        · apply div_nonneg <;> linarith
        · rw [div_le_one hpos]; linarith
      constructor
      · apply le_csInf hne
        rintro _ ⟨y, ⟨_, hy⟩, rfl⟩
        exact (hs y hy).1
      · refine csInf_le_of_le (b := slope (KS.J · (m, n)) K (K + 1)) ?_ ⟨K + 1, ⟨trivial, by linarith⟩, rfl⟩
          (hs (K + 1) (by linarith)).2
        refine ⟨0, ?_⟩
        rintro _ ⟨y, ⟨_, hy⟩, rfl⟩
        exact (hs y hy).1
    · intro a b h
      have := hconv.monotoneOn_rightDeriv (hint a) (hint b) h
      simp only
      rw [← derivWithin_Ioi_eq_Ici, ← derivWithin_Ioi_eq_Ici]
      exact this

theorem prop7611_core {β : ℝ} (KS : KStoppingValue β pMN) (m0 n0 : ℕ)
    (J0 : ℕ × ℕ → ℝ) (hJ0 : J0 = fun mn => KS.J (GittinsIndex KS (m0, n0)) mn) :
    ((∀ mn, J0 mn = max (pMN (m0, n0) + β * PMN J0 (m0, n0)) (pMN mn + β * PMN J0 mn)) ∧
        ∀ v : ℕ × ℕ → ℝ, (∃ C : ℝ, ∀ mn, |v mn| ≤ C) →
          (∀ mn, v mn = max (pMN (m0, n0) + β * PMN v (m0, n0)) (pMN mn + β * PMN v mn)) →
          v = J0) ∧
      GittinsIndex KS (m0, n0) = J0 (m0, n0) := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  set I := GittinsIndex KS (m0, n0) with hI
  have hind := gk_indiff KS (m0, n0)
  rw [← hI] at hind
  have hJ0' : ∀ mn, J0 mn = KS.J I mn := fun mn => by rw [hJ0]
  have hJ0f : J0 = KS.J I := funext hJ0'
  have hPI : pMN (m0, n0) + β * PMN J0 (m0, n0) = I := by
    rw [hJ0f]; exact hind.symm
  refine ⟨⟨fun mn => ?_, ?_⟩, ?_⟩
  · rw [hPI, hJ0f]; exact KS.hJ_fix I mn
  · intro v ⟨C, hC⟩ hv
    set c := pMN (m0, n0) + β * PMN v (m0, n0) with hc
    have hvJ : ∀ mn, v mn = KS.J c mn := by
      obtain ⟨C2, hC2⟩ := KS.hJ_bdd c
      intro mn
      apply le_antisymm
      · refine gk_comp KS.hβ0 KS.hβ1 KS.hq c c le_rfl v (KS.J c) (fun x => (hv x).le)
          (fun x => (KS.hJ_fix c x).ge) ⟨C + C2, fun x => ?_⟩ mn
        have := abs_le.1 (hC x); have := abs_le.1 (hC2 x); linarith
      · refine gk_comp KS.hβ0 KS.hβ1 KS.hq c c le_rfl (KS.J c) v (fun x => (KS.hJ_fix c x).le)
          (fun x => (hv x).ge) ⟨C + C2, fun x => ?_⟩ mn
        have := abs_le.1 (hC x); have := abs_le.1 (hC2 x); linarith
    have hvf : v = KS.J c := funext hvJ
    have hcc : c = pMN (m0, n0) + β * PQ pMN (KS.J c) (m0, n0) := by
      rw [hc]; conv_lhs => rw [hvf]
      rfl
    -- g strictly decreasing
    have gstrict : ∀ K K', K < K' →
        pMN (m0, n0) + β * PQ pMN (KS.J K') (m0, n0) - K' <
          pMN (m0, n0) + β * PQ pMN (KS.J K) (m0, n0) - K := by
      intro K K' h
      have h1 := gk_PQ_le_add KS.hq (KS.J K') (KS.J K) (K' - K) (fun x => gk_sub KS h.le x) (m0, n0)
      nlinarith
    have hcI : c = I := by
      rcases lt_trichotomy c I with h | h | h
      · have := gstrict c I h
        change _ < _ - c at this
        have e1 : pMN (m0, n0) + β * PQ pMN (KS.J I) (m0, n0) - I = 0 := by
          change _ = _ at hind; linarith
        linarith
      · exact h
      · have := gstrict I c h
        have e1 : pMN (m0, n0) + β * PQ pMN (KS.J I) (m0, n0) - I = 0 := by
          change _ = _ at hind; linarith
        linarith
    rw [hvf, hcI, hJ0f]
  · rw [hJ0', gk_sinf_mem]

end MDPFinance.InfiniteHorizonApplications

open MDPFinance.InfiniteHorizonApplications


theorem solution {β : ℝ} (KS : KStoppingValue β pMN) (m n : ℕ) :
    (Monotone (KS.J · (m, n)) ∧ Continuous (KS.J · (m, n)) ∧ ConvexOn ℝ Set.univ (KS.J · (m, n))) ∧
      Antitone (fun K => KS.J K (m, n) - K) ∧
      ((∀ K, GittinsIndex KS (m, n) ≤ K → KS.J K (m, n) = K) ∧
        (∀ K, K < GittinsIndex KS (m, n) →
          KS.J K (m, n) = pMN (m, n) + β * PMN (KS.J K) (m, n)) ∧
        ∀ K, K ≤ KS.J K (m, n) ∧ KS.J K (m, n) ≤ max K (GittinsIndex KS (m, n))) ∧
      (∃ N : Set ℝ, MeasureTheory.volume N = 0 ∧
        (∀ K ∉ N, DifferentiableAt ℝ (KS.J · (m, n)) K) ∧
        (∀ K, DifferentiableWithinAt ℝ (KS.J · (m, n)) (Set.Ici K) K ∧
          DifferentiableWithinAt ℝ (KS.J · (m, n)) (Set.Iic K) K) ∧
        (∀ K, 0 ≤ derivWithin (KS.J · (m, n)) (Set.Ici K) K ∧
          derivWithin (KS.J · (m, n)) (Set.Ici K) K ≤ 1) ∧
        Monotone fun K => derivWithin (KS.J · (m, n)) (Set.Ici K) K) := by
  exact prop767_core KS m n
