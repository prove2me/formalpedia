-- Prove2me | solution 1 for OAI.Problem326.global_bounded_persistent_solution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:04:47.718927+00:00
-- url     : https://prove2.me/submissions/78912448-dbb8-4fb4-b913-e3be7b1dfcca

import Mathlib
import Definitions.Def_MassAction

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe uIota uX uI uAlpha uBeta uEta uE uJ uLambda uV uF

section
section
namespace OAI


open Set Filter
open scoped Topology

namespace Problem326

/-- A positive derivative gives strict increase immediately to the right. -/
lemma eventually_lt_right_of_hasDerivAt_pos {f : ℝ → ℝ} {f' t : ℝ}
    (hf : HasDerivAt f f' t) (hpos : 0 < f') :
    ∀ᶠ u in 𝓝[>] t, f t < f u := by
  have hs := hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  filter_upwards [hs.eventually (Ioi_mem_nhds hpos), self_mem_nhdsWithin] with u hu htu
  have hdiv : 0 < (f u - f t) / (u - t) := by
    simpa only [slope_def_field] using hu
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr htu)).mp hdiv)

/-- Finite lower envelopes increase to the right when every active branch has
strictly positive derivative. Inactive branches only need continuity. -/
lemma finite_minimum_eventually_lt_right {ι : Type uIota} (s : Finset ι)
    (hne : s.Nonempty) (f : ι → ℝ → ℝ) (t : ℝ)
    (hcont : ∀ i ∈ s, ContinuousWithinAt (f i) (Ioi t) t)
    (hderiv : ∀ i ∈ s, s.inf' hne (fun j => f j t) = f i t →
      ∃ v : ℝ, HasDerivAt (f i) v t ∧ 0 < v) :
    ∀ᶠ u in 𝓝[>] t, s.inf' hne (fun j => f j t) < s.inf' hne (fun j => f j u) := by
  have heach : ∀ i ∈ s, ∀ᶠ u in 𝓝[>] t, s.inf' hne (fun j => f j t) < f i u := by
    intro i hi
    by_cases heq : s.inf' hne (fun j => f j t) = f i t
    · rcases hderiv i hi heq with ⟨v, hv, hpos⟩
      simpa only [heq] using eventually_lt_right_of_hasDerivAt_pos hv hpos
    · have hlt : s.inf' hne (fun j => f j t) < f i t :=
        lt_of_le_of_ne (Finset.inf'_le _ hi) heq
      exact (hcont i hi).eventually (Ioi_mem_nhds hlt)
  filter_upwards [(s.eventually_all).mpr heach] with u hu
  exact (Finset.lt_inf'_iff hne).mpr hu

/-- Adding the same constant commutes with a finite minimum. -/
lemma finite_minimum_add_const {ι : Type uIota} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) :
    s.inf' hne (fun i => f i + c) = s.inf' hne f + c := by
  apply le_antisymm
  · rcases s.exists_mem_eq_inf' hne f with ⟨i, hi, heq⟩
    rw [heq]
    exact Finset.inf'_le _ hi
  · exact (Finset.le_inf'_iff hne _).mpr fun i hi =>
      by simpa only [add_comm] using add_le_add_right (Finset.inf'_le f hi) c

/-- A finite minimum whose active branches have nonnegative derivatives is
nondecreasing. The left endpoint is included in the derivative hypothesis. -/
theorem finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg
    {ι : Type uIota} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (a b : ℝ)
    (hcont : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, ∀ i ∈ s,
      s.inf' hne (fun j => f j t) = f i t →
      ∃ v : ℝ, HasDerivAt (f i) v t ∧ 0 ≤ v) :
    MonotoneOn (fun t => s.inf' hne (fun i => f i t)) (Icc a b) := by
  let F : ℝ → ℝ := fun t => s.inf' hne (fun i => f i t)
  have hF : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hne hcont
  intro u hu v hv huv
  change F u ≤ F v
  have hpert : ∀ ε : ℝ, 0 < ε → F u + ε * u ≤ F v + ε * v := by
    intro ε hε
    let g : ι → ℝ → ℝ := fun i t => f i t + ε * t
    let G : ℝ → ℝ := fun t => F t + ε * t
    have hG : ContinuousOn G (Icc u v) :=
      (hF.add (continuousOn_const.mul continuousOn_id)).mono
        (Icc_subset_Icc hu.1 hv.2)
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr huv) hG
    have htv : t = v := by
      by_contra hne_tv
      have hlt : t < v := lt_of_le_of_ne ht.2 hne_tv
      have htab : t ∈ Ico a b := ⟨hu.1.trans ht.1, hlt.trans_le hv.2⟩
      have hevent : ∀ᶠ z in 𝓝[>] t, G t < G z := by
        have hm := finite_minimum_eventually_lt_right s hne g t
          (fun i hi => ((hcont i hi).add
            (continuousOn_const.mul continuousOn_id) t (Ico_subset_Icc_self htab)).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGT_of_mem htab))
          (by
            intro i hi hactive
            have hactive' : s.inf' hne (fun j => f j t) = f i t := by
              simpa only [g, finite_minimum_add_const, add_left_inj] using hactive
            obtain ⟨w, hw, hwpos⟩ := hderiv t htab i hi hactive'
            refine ⟨w + ε, ?_, by linarith⟩
            convert! hw.add ((hasDerivAt_id t).const_mul ε) using 1; simp)
        simpa only [g, finite_minimum_add_const, G, F] using hm
      obtain ⟨z, hz, htz⟩ := (hevent.and (Ioc_mem_nhdsGT hlt)).exists
      exact (not_lt_of_ge (hmax ⟨ht.1.trans htz.1.le, htz.2⟩)) hz
    subst t
    exact hmax (left_mem_Icc.mpr huv)
  have hlim : ContinuousWithinAt (fun ε : ℝ => F v + ε * (v - u)) (Ioi 0) 0 := by
    fun_prop
  have hle : ∀ ε ∈ Ioi (0 : ℝ), F u ≤ F v + ε * (v - u) := by
    intro ε hε
    have := hpert ε hε
    nlinarith
  have := ContinuousWithinAt.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0))
    continuousWithinAt_const hlim hle
  simpa using this

/-- Endpoint-continuous version: no derivatives are required at the endpoints. -/
theorem finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg_Ioo
    {ι : Type uIota} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (a b : ℝ)
    (hcont : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, ∀ i ∈ s,
      s.inf' hne (fun j => f j t) = f i t →
      ∃ v : ℝ, HasDerivAt (f i) v t ∧ 0 ≤ v) :
    MonotoneOn (fun t => s.inf' hne (fun i => f i t)) (Icc a b) := by
  let F : ℝ → ℝ := fun t => s.inf' hne (fun i => f i t)
  have hF : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hne hcont
  intro u hu v hv huv
  change F u ≤ F v
  rcases eq_or_lt_of_le huv with rfl | huv
  · exact le_rfl
  have hle : ∀ t ∈ Ioo u v, F t ≤ F v := by
    intro t ht
    have htv : t ≤ v := ht.2.le
    have hat : a < t := hu.1.trans_lt ht.1
    have hm := finite_minimum_monotoneOn_Icc_of_active_deriv_nonneg s hne f t v
      (fun i hi => (hcont i hi).mono (Icc_subset_Icc hat.le hv.2))
      (fun r hr i hi hactive => hderiv r ⟨hat.trans_le hr.1, hr.2.trans_le hv.2⟩
        i hi hactive)
    exact hm (left_mem_Icc.mpr htv) (right_mem_Icc.mpr htv) htv
  exact ContinuousWithinAt.closure_le
    (by rw [closure_Ioo huv.ne]; exact left_mem_Icc.mpr huv.le)
    ((hF u hu).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc hu.1 hv.2)))
    continuousWithinAt_const hle

end Problem326

end OAI
end
end

section
section
namespace OAI


/-! Topological compactness tools for the affine-label construction.
These lemmas concern an arbitrary activity relation, so no continuity in the
small parameter or in the label-dependent tolerance is assumed. -/

open Set Filter
open scoped Topology

namespace Problem326.AffineApproximation

variable {X : Type uX} {I : Type uI}

section Topological

variable [TopologicalSpace X]

/-- Points at which a label is active for some positive parameter below `δ`. -/
def smallActivity (A : ℝ → X → I → Prop) (δ : ℝ) (i : I) : Set X :=
  {x | ∃ h : ℝ, 0 < h ∧ h < δ ∧ A h x i}

/-- All limiting activity points as the positive parameter tends to zero. -/
def limitActivity (A : ℝ → X → I → Prop) (i : I) : Set X :=
  ⋂ δ : {δ : ℝ // 0 < δ}, closure (smallActivity A δ i)

theorem isClosed_limitActivity (A : ℝ → X → I → Prop) (i : I) :
    IsClosed (limitActivity A i) :=
  isClosed_iInter fun _ => isClosed_closure

omit [TopologicalSpace X] in
theorem smallActivity_mono (A : ℝ → X → I → Prop) (i : I)
    {δ ε : ℝ} (hδε : δ ≤ ε) : smallActivity A δ i ⊆ smallActivity A ε i := by
  rintro x ⟨h, hh, hδ, hA⟩
  exact ⟨h, hh, hδ.trans_le hδε, hA⟩

/-- A compact set whose limiting activity points all lie in an open set has
uniformly small activity in that open set. -/
theorem uniform_activity_one [T2Space X]
    (A : ℝ → X → I → Prop) (i : I) {K G : Set X}
    (hK : IsCompact K) (hG : IsOpen G)
    (hlim : K ∩ limitActivity A i ⊆ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ x ∈ K, A h x i → x ∈ G := by
  let V : {δ : ℝ // 0 < δ} → Set X :=
    fun δ => K ∩ closure (smallActivity A δ i)
  have hdir : Directed (· ⊇ ·) V := by
    intro δ ε
    refine ⟨⟨min δ.val ε.val, lt_min δ.property ε.property⟩, ?_, ?_⟩
    · exact inter_subset_inter_right K (closure_mono (smallActivity_mono A i (min_le_left _ _)))
    · exact inter_subset_inter_right K (closure_mono (smallActivity_mono A i (min_le_right _ _)))
  have hcpct : ∀ δ, IsCompact (V δ) :=
    fun _ => hK.inter_right isClosed_closure
  have hclosed : ∀ δ, IsClosed (V δ) :=
    fun _ => hK.isClosed.inter isClosed_closure
  have hnhds : ∀ x ∈ ⋂ δ, V δ, G ∈ 𝓝 x := by
    intro x hx
    have hmem : ∀ δ, x ∈ V δ := mem_iInter.mp hx
    apply hG.mem_nhds
    apply hlim
    refine ⟨(hmem ⟨1, zero_lt_one⟩).1, ?_⟩
    exact mem_iInter.mpr fun δ => (hmem δ).2
  have : Nonempty {δ : ℝ // 0 < δ} := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨δ, hδ⟩ := exists_subset_nhds_of_isCompact' hdir hcpct hclosed hnhds
  refine ⟨δ.val, δ.property, ?_⟩
  intro h hh hsmall x hx hactive
  exact hδ ⟨hx, subset_closure ⟨h, hh, hsmall, hactive⟩⟩

/-- Uniformity holds simultaneously for a finite family of labels. -/
theorem uniform_activity [T2Space X] [Fintype I]
    (A : ℝ → X → I → Prop) {K : Set X} (G : I → Set X)
    (hK : IsCompact K) (hG : ∀ i, IsOpen (G i))
    (hlim : ∀ i, K ∩ limitActivity A i ⊆ G i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ x ∈ K, ∀ i, A h x i → x ∈ G i := by
  classical
  obtain hI | hI := isEmpty_or_nonempty I
  · exact ⟨1, zero_lt_one, fun _ _ _ _ _ i => isEmptyElim i⟩
  · choose δ hδ hbound using fun i => uniform_activity_one A i hK (hG i) (hlim i)
    let δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
    have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff _).mpr (fun i _ => hδ i)
    refine ⟨δ₀, hδ₀, ?_⟩
    intro h hh hsmall x hx i hi
    apply hbound i h hh _ x hx hi
    exact hsmall.trans_le (Finset.inf'_le δ (Finset.mem_univ i))

/-- The fixed-minimum guarantee extends to a neighborhood of that minimum.
Only the finitely many fixed tolerance values are used. -/
theorem nearby_level_activity [Finite I]
    (A : ℝ → X → I → Prop) {K : Set X} (hK : IsCompact K)
    (μ : X → ℝ) (hμ : Continuous μ) (t : ℝ)
    (err : I → X → ℝ) (herr : ∀ i, Continuous (err i)) (E : I → ℝ)
    (hgood : ∀ i, ∀ p ∈ K, p ∈ limitActivity A i → μ p = t → err i p < E i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ∀ p ∈ K,
      p ∈ limitActivity A i → |μ p - t| < ρ → err i p < E i := by
  let B : Set X := ⋃ i, K ∩ (limitActivity A i ∩ {p | E i ≤ err i p})
  have hB : IsCompact B := by
    apply isCompact_iUnion
    intro i
    exact hK.inter_right ((isClosed_limitActivity A i).inter
      (isClosed_le continuous_const (herr i)))
  have ht : t ∉ μ '' B := by
    rintro ⟨p, hp, hpt⟩
    obtain ⟨i, hpK, hplim, hpbad⟩ := mem_iUnion.mp hp
    exact (not_lt_of_ge hpbad) (hgood i p hpK hplim hpt)
  have hnhds : (μ '' B)ᶜ ∈ 𝓝 t := (hB.image hμ).isClosed.isOpen_compl.mem_nhds ht
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ρ, hρ, ?_⟩
  intro i p hp hplim hclose
  by_contra hbad
  have hpB : p ∈ B := mem_iUnion.mpr ⟨i, hp, hplim, le_of_not_gt hbad⟩
  have hpball : μ p ∈ Metric.ball t ρ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hclose
  exact (hball hpball) ⟨p, hpB, rfl⟩

end Topological

section Metric

variable [PseudoMetricSpace X]

theorem mem_limitActivity_iff_seq (A : ℝ → X → I → Prop) (i : I) (p : X) :
    p ∈ limitActivity A i ↔
      ∃ h : ℕ → ℝ, ∃ x : ℕ → X,
        (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
        Tendsto x atTop (𝓝 p) ∧ ∀ n, A (h n) (x n) i := by
  constructor
  · intro hp
    have hchoice : ∀ n : ℕ, ∃ x ∈ smallActivity A (1 / ((n : ℝ) + 1)) i,
        dist p x < 1 / ((n : ℝ) + 1) := by
      intro n
      have he : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact Metric.mem_closure_iff.mp (mem_iInter.mp hp ⟨_, he⟩) _ he
    choose x hx hdist using hchoice
    choose h hpos hsmall hA using hx
    refine ⟨h, x, hpos, ?_, ?_, hA⟩
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat
        (fun n => (hpos n).le) (fun n => (hsmall n).le)
    · apply tendsto_iff_dist_tendsto_zero.mpr
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat
      · intro n
        exact dist_nonneg
      · intro n
        simpa only [dist_comm] using (hdist n).le
  · rintro ⟨h, x, hpos, hh, hx, hA⟩
    apply mem_iInter.mpr
    intro δ
    apply isClosed_closure.mem_of_tendsto hx
    filter_upwards [hh.eventually_lt_const δ.property] with n hn
    exact subset_closure ⟨h n, hpos n, hn, hA n⟩

/-- Uniform activity bound in exactly the sequential form used by the affine
approximation lemma. -/
theorem uniform_activity_of_sequence [T2Space X] [Fintype I]
    (A : ℝ → X → I → Prop) {K : Set X} (hK : IsCompact K)
    (err : I → X → ℝ) (herr : ∀ i, Continuous (err i)) (E : I → ℝ)
    (hseq : ∀ i, ∀ p ∈ K, ∀ h : ℕ → ℝ, ∀ x : ℕ → X,
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) → Tendsto x atTop (𝓝 p) →
      (∀ n, A (h n) (x n) i) → err i p < E i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, ∀ i, A h p i → err i p < E i := by
  apply uniform_activity A (fun i => {p | err i p < E i}) hK
  · intro i
    exact isOpen_lt (herr i) continuous_const
  · intro i p hp
    obtain ⟨h, x, hpos, hh, hx, hA⟩ := (mem_limitActivity_iff_seq A i p).mp hp.2
    exact hseq i p hp.1 h x hpos hh hx hA

end Metric

end Problem326.AffineApproximation

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators
open Filter Topology

namespace Problem326.Affine

structure Label (d : ℕ) where
  slope : Fin d → ℝ
  offset : ℝ → ℝ

def Label.value {d : ℕ} (L : Label d) (h : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, L.slope i * x i + L.offset h

def Active {d : ℕ} (Λ : Finset (Label d)) (L : Label d)
    (h : ℝ) (x : Fin d → ℝ) : Prop :=
  L ∈ Λ ∧ ∀ J ∈ Λ, L.value h x ≤ J.value h x

def Cube {d : ℕ} (a b : ℝ) (p : Fin d → ℝ) : Prop :=
  ∀ i, a ≤ p i ∧ p i ≤ b

def HasMinimum {d : ℕ} (p : Fin d → ℝ) (t : ℝ) : Prop :=
  (∀ i, t ≤ p i) ∧ ∃ i, p i = t

def powerPoint {d : ℕ} (h : ℝ) (p : Fin d → ℝ) : Fin d → ℝ :=
  fun i => h ^ p i

/-- The sequential condition required of a family at one fixed minimum level. -/
def ApproximatesAtMinimum {d : ℕ} (Λ : Finset (Label d))
    (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ → HasMinimum p₀ t →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

lemma active_mono {d : ℕ} {Λ Γ : Finset (Label d)} {L : Label d}
    {h : ℝ} {x : Fin d → ℝ} (hΛ : Λ ⊆ Γ) (hL : L ∈ Λ)
    (ha : Active Γ L h x) : Active Λ L h x :=
  ⟨hL, fun J hJ => ha.2 J (hΛ hJ)⟩

lemma active_singleton {d : ℕ} (L : Label d) (h : ℝ) (x : Fin d → ℝ) :
    Active {L} L h x := by
  classical
  refine ⟨by simp, ?_⟩
  intro J hJ
  have hJL : J = L := by simpa using hJ
  subst J
  exact le_rfl

/-- Comparison activity is insensitive to a common additive shift. -/
lemma active_iff_common_shift {ι : Type uIota} (s : Finset ι) (v : ι → ℝ)
    (i : ι) (c : ℝ) :
    (∀ j ∈ s, v i + c ≤ v j + c) ↔ (∀ j ∈ s, v i ≤ v j) := by
  simp only [add_le_add_iff_right]

lemma exists_active {d : ℕ} (Λ : Finset (Label d)) (hne : Λ.Nonempty)
    (h : ℝ) (x : Fin d → ℝ) : ∃ L, Active Λ L h x := by
  classical
  obtain ⟨L, hL, hmin⟩ := Λ.exists_min_image (fun J => J.value h x) hne
  exact ⟨L, hL, hmin⟩

/-- A finite collection of positive tolerances admits one strict common bound. -/
lemma exists_common_pos_lt {ι : Type uIota} (s : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ s, 0 < E i) (u : ℝ) (hu : 0 < u) :
    ∃ δ : ℝ, 0 < δ ∧ δ < u ∧ ∀ i ∈ s, δ < E i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨u / 2, by positivity, by linarith, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨δ, hδ, hδu, hδE⟩ := ih (fun j hj => hE j (Finset.mem_insert_of_mem hj))
      have hEi : 0 < E i := hE i (Finset.mem_insert_self _ _)
      refine ⟨min δ (E i / 2), lt_min hδ (by positivity),
        (min_le_left _ _).trans_lt hδu, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt (by linarith)
      · exact (min_le_left _ _).trans_lt (hδE j hj)

/-- The choice of the next type threshold in the fixed-minimum induction.
The upper endpoint can itself be the preceding threshold, giving a decreasing
sequence while only querying finitely many tolerance values. -/
lemma exists_threshold {ι : Type uIota} (s : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ s, 0 < E i) {t u : ℝ} (htu : t < u) :
    ∃ β : ℝ, t < β ∧ β < u ∧ ∀ i ∈ s, β - t < E i := by
  obtain ⟨δ, hδ, hδu, hδE⟩ := exists_common_pos_lt s E hE (u - t) (sub_pos.mpr htu)
  refine ⟨t + δ, by linarith, by linarith, ?_⟩
  intro i hi
  simpa using hδE i hi

lemma eq_const_of_minimum_at_upper {d : ℕ} {a b : ℝ} {p : Fin d → ℝ}
    (hp : Cube a b p) (hm : HasMinimum p b) : p = fun _ => b := by
  funext i
  exact le_antisymm (hp i).2 (hm.1 i)

lemma eq_const_of_minimum_one {p : Fin 1 → ℝ} {t : ℝ}
    (hm : HasMinimum p t) : p = fun _ => t := by
  obtain ⟨i, hi⟩ := hm.2
  funext j
  have hij : j = i := Subsingleton.elim _ _
  simpa [hij] using hi

/-- Final coordinate estimate for types with a further threshold. -/
lemma norm_sub_lt_of_support {d : ℕ} (U : Finset (Fin d))
    {p r : Fin d → ℝ} {t β ε : ℝ} (hε : 0 < ε)
    (hin : ∀ i ∈ U, |p i - r i| < ε)
    (hout : ∀ i ∉ U, r i = t ∧ t ≤ p i ∧ p i ≤ β)
    (hβ : β - t < ε) : ‖p - r‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro i
  change |p i - r i| < ε
  by_cases hi : i ∈ U
  · exact hin i hi
  · obtain ⟨hr, hp, hpβ⟩ := hout i hi
    rw [hr, abs_of_nonneg (sub_nonneg.mpr hp)]
    linarith

/-- For the last type, the unique unraised coordinate realizes the minimum. -/
lemma off_support_eq_minimum {d : ℕ} (U : Finset (Fin d))
    {p : Fin d → ℝ} {t : ℝ} (hm : HasMinimum p t)
    (hin : ∀ i ∈ U, t < p i) (hcomp : ∀ i ∉ U, ∀ j ∉ U, i = j) :
    ∀ i ∉ U, p i = t := by
  obtain ⟨j, hj⟩ := hm.2
  have hjU : j ∉ U := by
    intro hjU
    have := hin j hjU
    linarith
  intro i hi
  have hij : i = j := hcomp i hi j hjU
  simpa [hij] using hj

/-- The singleton family verifies the fixed-minimum base case in dimension one. -/
lemma singleton_approximates_one (a b t : ℝ) (E : (Fin 1 → ℝ) → ℝ)
    (hE : 0 < E (fun _ => t)) :
    ApproximatesAtMinimum {⟨fun _ => t, fun _ => 0⟩} a b t E := by
  classical
  intro L hL h p p₀ hh hlim hp hp₀ hm ha
  have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
  subst L
  rw [eq_const_of_minimum_one hm]
  simpa using hE

/-- The other singleton base case works in every dimension at the upper corner. -/
lemma singleton_approximates_upper {d : ℕ} (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ) (hE : 0 < E (fun _ => b)) :
    ApproximatesAtMinimum {⟨fun _ => b, fun _ => 0⟩} a b b E := by
  classical
  intro L hL h p p₀ hh hlim hp hp₀ hm ha
  have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
  subst L
  rw [eq_const_of_minimum_at_upper hp₀ hm]
  simpa using hE

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

/-! Certificates for the dimension induction and interval gluing.

In particular a local certificate retains a strictly stronger offset decay
exponent. Merely retaining `o(h^t)` would not suffice for interval gluing.
-/

noncomputable section
open Filter Topology

namespace Problem326.Affine

/-- Sequential approximation on the whole exponent cube, allowing the
approximating sequence to lie outside the cube. -/
def SequentialApproximation {d : ℕ} (Λ : Finset (Label d))
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- The conclusion of the affine approximation lemma in one dimension `d`.
The label set and its slopes are fixed before a small parameter is chosen. -/
structure FullCertificate (d : ℕ) (a b : ℝ) (E : (Fin d → ℝ) → ℝ) where
  labels : Finset (Label d)
  nonempty : labels.Nonempty
  slopes : ∀ L ∈ labels, Cube a b L.slope
  offsets : ∀ L ∈ labels,
    L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a)
  approximation : SequentialApproximation labels a b E

/-- The output required at a fixed minimum before neighborhood extension.
`decay_gt` and `offsets` are essential data for the subsequent gluing step. -/
structure LocalCertificate (d : ℕ) (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) where
  labels : Finset (Label d)
  baseline : (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ labels
  slopes : ∀ L ∈ labels, Cube t b L.slope
  minima : ∀ L ∈ labels, HasMinimum L.slope t
  decayExponent : ℝ
  decay_gt : t < decayExponent
  offsets : ∀ L ∈ labels,
    L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ decayExponent)
  approximation : ApproximatesAtMinimum labels a b t E

lemma LocalCertificate.nonempty {d : ℕ} {a b t : ℝ}
    {E : (Fin d → ℝ) → ℝ} (C : LocalCertificate d a b t E) : C.labels.Nonempty :=
  ⟨_, C.baseline⟩

/-- The fixed-minimum singleton construction in species dimension one. -/
def localCertificate_one (a b t : ℝ) (htb : t ≤ b)
    (E : (Fin 1 → ℝ) → ℝ) (hE : 0 < E (fun _ => t)) :
    LocalCertificate 1 a b t E := by
  classical
  refine {
    labels := {⟨fun _ => t, fun _ => 0⟩}
    baseline := by simp
    slopes := ?_
    minima := ?_
    decayExponent := t + 1
    decay_gt := by linarith
    offsets := ?_
    approximation := singleton_approximates_one a b t E hE
  }
  · intro L hL
    have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
    subst L
    exact fun _ => ⟨le_rfl, htb⟩
  · intro L hL
    have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
    subst L
    exact ⟨fun _ => le_rfl, ⟨0, rfl⟩⟩
  · intro L hL
    have hL' : L = (⟨fun _ => t, fun _ => 0⟩ : Label 1) := by simpa using hL
    subst L
    exact Asymptotics.isLittleO_zero _ _

/-- The fixed-minimum singleton construction at the upper corner. -/
def localCertificate_upper {d : ℕ} (hd : 0 < d) (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ) (hE : 0 < E (fun _ => b)) :
    LocalCertificate d a b b E := by
  classical
  refine {
    labels := {⟨fun _ => b, fun _ => 0⟩}
    baseline := by simp
    slopes := ?_
    minima := ?_
    decayExponent := b + 1
    decay_gt := by linarith
    offsets := ?_
    approximation := singleton_approximates_upper a b E hE
  }
  · intro L hL
    have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
    subst L
    exact fun _ => ⟨le_rfl, le_rfl⟩
  · intro L hL
    have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
    subst L
    exact ⟨fun _ => le_rfl, ⟨⟨0, hd⟩, rfl⟩⟩
  · intro L hL
    have hL' : L = (⟨fun _ => b, fun _ => 0⟩ : Label d) := by simpa using hL
    subst L
    exact Asymptotics.isLittleO_zero _ _

/-- Harmless dimension-zero base for strong induction. It is not used as a
positive-dimensional fixed-minimum family. -/
def fullCertificate_zero (a b : ℝ) (E : (Fin 0 → ℝ) → ℝ)
    (hE : ∀ r, Cube a b r → 0 < E r) : FullCertificate 0 a b E := by
  classical
  let L : Label 0 := ⟨fun _ => a, fun _ => 0⟩
  refine {
    labels := {L}
    nonempty := Finset.singleton_nonempty L
    slopes := ?_
    offsets := ?_
    approximation := ?_
  }
  · intro J hJ i
    exact Fin.elim0 i
  · intro J hJ
    have hJL : J = L := by simpa using hJ
    subst J
    exact Asymptotics.isLittleO_zero _ _
  · intro J hJ h p p₀ hh hhlim hp hp₀ ha
    have hJL : J = L := by simpa using hJ
    subst J
    have heq : p₀ = L.slope := by funext i; exact Fin.elim0 i
    rw [heq, sub_self, norm_zero]
    exact hE L.slope (fun i => Fin.elim0 i)

/-- Strong induction assembles full certificates from fixed-minimum
certificates and finite interval gluing. -/
theorem fullCertificate_of_local_and_glue
    (construct : ∀ d : ℕ, 0 < d →
      (∀ k : ℕ, k < d → ∀ a b : ℝ, ∀ E : (Fin k → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate k a b E)) →
      ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) →
        ∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E))
    (glue : ∀ d : ℕ, 0 < d → ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      (∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E)) →
      Nonempty (FullCertificate d a b E)) :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate d a b E) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro a b E hab hE
      by_cases hd : d = 0
      · subst d
        exact ⟨fullCertificate_zero a b E hE⟩
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        exact glue d hdpos a b E hab hE (construct d hdpos ih a b E hab hE)

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace Problem326.FixedMinimum

/-- The affine value relative to the constant-slope branch `t`. -/
def relativeValue {ι : Type uIota} [Fintype ι]
    (t : ℝ) (r p : ι → ℝ) (h c : ℝ) : ℝ :=
  (∑ i, (r i - t) * h ^ p i) + c

/-- A strict limiting exponent gap makes the normalized monomial vanish.
This formulation permits the approximating exponents to leave their cube. -/
theorem tendsto_rpow_ratio {h p : ℕ → ℝ} {q p₀ : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀)) (hqp : q < p₀) :
    Tendsto (fun n => h n ^ p n / h n ^ q) atTop (𝓝 0) := by
  have hlim := hh0.rpow (hp.sub_const q) (Or.inr (sub_pos.mpr hqp))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hqp))] at hlim
  convert hlim using 1
  ext n
  exact (Real.rpow_sub (hh n) (p n) q).symm

/-- Finite sums of monomials whose nonzero coefficients have exponent above `q`
are negligible relative to `h^q`. -/
theorem tendsto_normalized_sum {ι : Type uIota} [Fintype ι]
    {h : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ a : ι → ℝ} {q : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hgap : ∀ i, a i ≠ 0 → q < p₀ i) :
    Tendsto (fun n => (∑ i, a i * h n ^ p n i) / h n ^ q)
      atTop (𝓝 0) := by
  have hterm : ∀ i, Tendsto (fun n => a i * (h n ^ p n i / h n ^ q))
      atTop (𝓝 0) := by
    intro i
    by_cases hai : a i = 0
    · simp [hai]
    · simpa using (tendsto_rpow_ratio hh hh0 (hp i) (hgap i hai)).const_mul (a i)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  simpa only [Finset.sum_const_zero, Finset.sum_div, mul_div_assoc] using hs

/-- A positive coefficient in a nonnegative sum cannot be dominated by a
strictly higher exponent, even in the presence of a negligible offset. -/
theorem coefficient_nonpos_of_domination
    {A B d : ℕ → ℝ} {c : ℝ}
    (hA : ∀ n, 0 < A n) (hB : ∀ n, 0 < B n)
    (hBA : Tendsto (fun n => B n / A n) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / B n) atTop (𝓝 0))
    (hdom : ∀ n, c * A n ≤ B n - d n) : c ≤ 0 := by
  have hlim : Tendsto (fun n => (B n / A n) * (1 - d n / B n))
      atTop (𝓝 0) := by
    simpa using hBA.mul (tendsto_const_nhds.sub hd)
  apply ge_of_tendsto hlim
  filter_upwards [] with n
  have h := (le_div_iff₀ (hA n)).2 (hdom n)
  convert h using 1
  field_simp [ne_of_gt (hA n), ne_of_gt (hB n)]

/-- The quotient version also allows a moving denominator exponent. -/
theorem tendsto_rpow_ratio_of_gap {h p q : ℕ → ℝ} {p₀ q₀ : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 q₀))
    (hqp : q₀ < p₀) :
    Tendsto (fun n => h n ^ p n / h n ^ q n) atTop (𝓝 0) := by
  have hlim := hh0.rpow (hp.sub hq) (Or.inr (sub_pos.mpr hqp))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hqp))] at hlim
  convert hlim using 1
  ext n
  exact (Real.rpow_sub (hh n) (p n) (q n)).symm

/-- Nonnegative raised coordinates of an active branch cannot have limiting
exponent below the offset exponent. -/
theorem active_raised_exponent_ge {ι : Type uIota} [Fintype ι]
    {h c : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r : ι → ℝ} {t β : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hr : ∀ i, t ≤ r i)
    (hc : Tendsto (fun n => c n / h n ^ β) atTop (𝓝 (-1)))
    (hactive : ∀ n, relativeValue t r (p n) (h n) (c n) ≤ 0)
    {i : ι} (hi : t < r i) : β ≤ p₀ i := by
  by_contra hle
  have hlt : p₀ i < β := lt_of_not_ge hle
  have hratio : Tendsto (fun n => h n ^ β / h n ^ p n i) atTop (𝓝 0) :=
    tendsto_rpow_ratio_of_gap hh hh0 tendsto_const_nhds (hp i) hlt
  have hlim : Tendsto (fun n => (-c n / h n ^ β) *
      (h n ^ β / h n ^ p n i)) atTop (𝓝 0) := by
    simpa only [neg_div, neg_neg, one_mul, mul_zero] using hc.neg.mul hratio
  have hnonpos : r i - t ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [] with n
    have hsingle : (r i - t) * h n ^ p n i ≤
        ∑ j, (r j - t) * h n ^ p n j := by
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (sub_nonneg.mpr (hr j)) (Real.rpow_nonneg (hh n).le _))
        (Finset.mem_univ i)
    have hbound : (r i - t) * h n ^ p n i ≤ -c n := by
      have ha := hactive n
      unfold relativeValue at ha
      linarith
    have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos (hh n) (p n i))).2 hbound
    convert hdiv using 1
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (hh n) β)]
  linarith

/-- A competitor with normalized value tending to `-1` defeats any branch
whose slope is coordinatewise above the baseline and whose normalized
offset tends to zero. No continuity of either offset is needed. -/
theorem not_active_of_offset_gap {ι : Type uIota} [Fintype ι]
    {h c d : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r s : ι → ℝ} {t γ : ℝ}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hr : ∀ i, t ≤ r i)
    (hc : Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / h n ^ γ) atTop (𝓝 (-1)))
    (hgap : ∀ i, s i ≠ t → γ < p₀ i) :
    ¬ (∀ n, relativeValue t r (p n) (h n) (c n) ≤
      relativeValue t s (p n) (h n) (d n)) := by
  intro hactive
  have hsum : Tendsto (fun n => (∑ i, (s i - t) * h n ^ p n i) /
      h n ^ γ) atTop (𝓝 0) :=
    tendsto_normalized_sum hh hh0 hp (fun i hi => hgap i (sub_ne_zero.mp hi))
  have hvalue : Tendsto (fun n => relativeValue t s (p n) (h n) (d n) /
      h n ^ γ) atTop (𝓝 (-1)) := by
    simpa only [relativeValue, add_div, zero_add] using hsum.add hd
  have hbad : (0 : ℝ) ≤ -1 := by
    apply le_of_tendsto_of_tendsto hc hvalue
    filter_upwards [] with n
    apply (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos (hh n) γ)).2
    have hsum0 : 0 ≤ ∑ i, (r i - t) * h n ^ p n i := by
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (sub_nonneg.mpr (hr i)) (Real.rpow_nonneg (hh n).le _)
    have ha := hactive n
    unfold relativeValue at ha ⊢
    linarith
  norm_num at hbad

/-- The second exclusion in the fixed-minimum argument. A next-type
competitor supported on `U ∪ {j}` forces every unraised exponent below
its offset threshold. -/
theorem unraised_exponent_le {ι : Type uIota} [Fintype ι] [DecidableEq ι]
    {h c d : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r s : ι → ℝ}
    {t β γ : ℝ} {U : Finset ι} {j : ι}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hr : ∀ i, t ≤ r i)
    (hc : Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / h n ^ γ) atTop (𝓝 (-1)))
    (hγβ : γ < β) (hpU : ∀ i ∈ U, β ≤ p₀ i)
    (hs : ∀ i, i ∉ U → i ≠ j → s i = t)
    (hactive : ∀ n, relativeValue t r (p n) (h n) (c n) ≤
      relativeValue t s (p n) (h n) (d n)) : p₀ j ≤ γ := by
  by_contra hj
  have hj' : γ < p₀ j := lt_of_not_ge hj
  apply not_active_of_offset_gap hh hh0 hp hr hc hd _ hactive
  intro i hi
  by_cases hiU : i ∈ U
  · exact hγβ.trans_le (hpU i hiU)
  · have hij : i = j := by
      by_contra hij
      exact hi (hs i hiU hij)
    simpa only [hij] using hj'

/-- When only one coordinate is unraised, the fixed minimum determines
that coordinate exactly. -/
theorem last_unraised_eq_minimum {ι : Type uIota} {p : ι → ℝ} {t β : ℝ} {j : ι}
    (hmin : ∃ i, p i = t) (htβ : t < β)
    (hother : ∀ i, i ≠ j → β ≤ p i) : p j = t := by
  obtain ⟨i, hi⟩ := hmin
  have hij : i = j := by
    by_contra hij
    have h := hother i hij
    rw [hi] at h
    exact (not_le_of_gt htβ) h
  simpa only [hij] using hi

/-- Combining the inductive error on raised coordinates with the threshold
bound on all other coordinates yields the full sup-norm error estimate. -/
theorem error_of_raised_and_unraised {ι : Type uIota} [Fintype ι]
    {p r : ι → ℝ} {U : Set ι} {t γ ε : ℝ}
    (hraised : ∀ i ∈ U, |p i - r i| < ε)
    (hr : ∀ i ∉ U, r i = t)
    (hlo : ∀ i ∉ U, t ≤ p i)
    (hhi : ∀ i ∉ U, p i ≤ γ) (hε : γ - t < ε) :
    ∀ i, |p i - r i| < ε := by
  intro i
  by_cases hi : i ∈ U
  · exact hraised i hi
  · rw [hr i hi, abs_of_nonneg (sub_nonneg.mpr (hlo i hi))]
    exact (sub_le_sub_right (hhi i hi) t).trans_lt hε

theorem fixed_minimum_label_bound {ι : Type uIota} [Fintype ι] [DecidableEq ι]
    {h c : ℕ → ℝ} {p : ℕ → ι → ℝ} {p₀ r : ι → ℝ}
    {t β ε : ℝ} {U : Finset ι}
    (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hp : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)))
    (hlo : ∀ i, t ≤ p₀ i) (hmin : ∃ i, p₀ i = t)
    (htβ : t < β) (hε : 0 < ε)
    (hrin : ∀ i ∈ U, β ≤ r i) (hrout : ∀ i ∉ U, r i = t)
    (hoffset : (U = ∅ ∧ ∀ n, c n = 0) ∨
      Tendsto (fun n => c n / h n ^ β) atTop (𝓝 (-1)))
    (hbase : ∀ n, relativeValue t r (p n) (h n) (c n) ≤ 0)
    (hind : (∀ i ∈ U, β ≤ p₀ i) → ∀ i ∈ U, |p₀ i - r i| < ε)
    (hnext : (∀ i ∉ U, ∀ j ∉ U, i = j) ∨
      ∃ γ : ℝ, γ < β ∧ γ - t < ε ∧
        ∀ j, j ∉ U → ∃ s : ι → ℝ, ∃ d : ℕ → ℝ,
          Tendsto (fun n => d n / h n ^ γ) atTop (𝓝 (-1)) ∧
          (∀ i, i ∉ U → i ≠ j → s i = t) ∧
          (∀ n, relativeValue t r (p n) (h n) (c n) ≤
            relativeValue t s (p n) (h n) (d n))) :
    ∀ i, |p₀ i - r i| < ε := by
  have hr : ∀ i, t ≤ r i := by
    intro i
    by_cases hi : i ∈ U
    · exact htβ.le.trans (hrin i hi)
    · rw [hrout i hi]
  have hpU : ∀ i ∈ U, β ≤ p₀ i := by
    intro i hi
    rcases hoffset with ⟨hU, _⟩ | hc
    · simp [hU] at hi
    · exact active_raised_exponent_ge hh hh0 hp hr hc hbase
        (htβ.trans_le (hrin i hi))
  have herrU := hind hpU
  rcases hnext with hlast | ⟨γ, hγβ, hγε, hcomp⟩
  · obtain ⟨j, hj⟩ := hmin
    have hjU : j ∉ U := by
      intro hjU
      have hb := hpU j hjU
      rw [hj] at hb
      exact (not_le_of_gt htβ) hb
    intro i
    by_cases hi : i ∈ U
    · exact herrU i hi
    · have hij := hlast i hi j hjU
      rw [hrout i hi, hij, hj, sub_self, abs_zero]
      exact hε
  · have hcγ : Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 0) := by
      rcases hoffset with ⟨_, hc⟩ | hc
      · have hz : (fun n => c n / h n ^ γ) = fun _ => 0 := by
          funext n
          simp only [hc n, zero_div]
        rw [hz]
        exact tendsto_const_nhds
      · have hratio := tendsto_rpow_ratio hh hh0
          (show Tendsto (fun _ : ℕ => β) atTop (𝓝 β) from tendsto_const_nhds) hγβ
        have hlim := hc.mul hratio
        simp only [mul_zero] at hlim
        convert hlim using 1
        funext n
        field_simp [ne_of_gt (Real.rpow_pos_of_pos (hh n) β)]
    have hpout : ∀ j ∉ U, p₀ j ≤ γ := by
      intro j hj
      obtain ⟨s, d, hd, hs, ha⟩ := hcomp j hj
      exact unraised_exponent_le hh hh0 hp hr hcγ hd hγβ hpU hs ha
    exact error_of_raised_and_unraised (U := (↑U : Set ι))
      herrU hrout (fun i _ => hlo i) hpout hγε

end Problem326.FixedMinimum

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter
open scoped Topology BigOperators

namespace Problem326.Affine

/-- The unshifted constant-slope label used at a fixed minimum level. -/
def constantLabel (d : ℕ) (t : ℝ) : Label d :=
  ⟨fun _ => t, fun _ => 0⟩

/-- Finite construction data for one label. The `inner_bound` field is exactly
what the lower-dimensional induction supplies after restricting activity to the
lifted family. All remaining fields concern finite choices or offset asymptotics. -/
structure FixedMinimumLabelCertificate {d : ℕ} (Λ : Finset (Label d))
    (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) (L : Label d) where
  support : Finset (Fin d)
  threshold : ℝ
  threshold_gt : t < threshold
  error_pos : 0 < E L.slope
  slope_in : ∀ i ∈ support, threshold ≤ L.slope i
  slope_out : ∀ i ∉ support, L.slope i = t
  offset_behavior :
    (support = ∅ ∧ ∀ h, L.offset h = 0) ∨
    Tendsto (fun h => L.offset h / h ^ threshold) (𝓝[>] 0) (𝓝 (-1))
  inner_bound : ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    (∀ i ∈ support, threshold ≤ p₀ i) →
    ∀ i ∈ support, |p₀ i - L.slope i| < E L.slope
  successor :
    (∀ i ∉ support, ∀ j ∉ support, i = j) ∨
    ∃ γ : ℝ, γ < threshold ∧ γ - t < E L.slope ∧
      ∀ j, j ∉ support → ∃ J ∈ Λ,
        Tendsto (fun h => J.offset h / h ^ γ) (𝓝[>] 0) (𝓝 (-1)) ∧
        (∀ i, i ∉ support → i ≠ j → J.slope i = t)

lemma relativeValue_eq_value_sub {d : ℕ} (L : Label d) (t h : ℝ)
    (p : Fin d → ℝ) :
    FixedMinimum.relativeValue t L.slope p h (L.offset h) =
      L.value h (powerPoint h p) - ∑ i, t * h ^ p i := by
  simp only [FixedMinimum.relativeValue, Label.value, powerPoint,
    sub_mul, Finset.sum_sub_distrib]
  ring

lemma active_relativeValue_le {d : ℕ} {Λ : Finset (Label d)}
    {L J : Label d} {h t : ℝ} {p : Fin d → ℝ}
    (hactive : Active Λ L h (powerPoint h p)) (hJ : J ∈ Λ) :
    FixedMinimum.relativeValue t L.slope p h (L.offset h) ≤
      FixedMinimum.relativeValue t J.slope p h (J.offset h) := by
  rw [relativeValue_eq_value_sub, relativeValue_eq_value_sub]
  exact sub_le_sub_right (hactive.2 J hJ) _

theorem approximatesAtMinimum_of_certificates {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hbaseline : constantLabel d t ∈ Λ)
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    ApproximatesAtMinimum Λ a b t E := by
  intro L hL h p p₀ hh hh0 hp hcube hm ha
  let C := hcert L hL
  have hhGT : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh0, Filter.Eventually.of_forall hh⟩
  have hpcoord : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)) :=
    tendsto_pi_nhds.mp hp
  have hbase : ∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n)
      (L.offset (h n)) ≤ 0 := by
    intro n
    have hv := active_relativeValue_le (t := t) (ha n) hbaseline
    simpa only [constantLabel, FixedMinimum.relativeValue, sub_self,
      zero_mul, Finset.sum_const_zero, add_zero] using hv
  have hoffset : (C.support = ∅ ∧ ∀ n, L.offset (h n) = 0) ∨
      Tendsto (fun n => L.offset (h n) / h n ^ C.threshold) atTop (𝓝 (-1)) := by
    rcases C.offset_behavior with ⟨hU, hc⟩ | hc
    · exact Or.inl ⟨hU, fun n => hc (h n)⟩
    · exact Or.inr (hc.comp hhGT)
  have hnext : (∀ i ∉ C.support, ∀ j ∉ C.support, i = j) ∨
      ∃ γ : ℝ, γ < C.threshold ∧ γ - t < E L.slope ∧
        ∀ j, j ∉ C.support → ∃ s : Fin d → ℝ, ∃ c : ℕ → ℝ,
          Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 (-1)) ∧
          (∀ i, i ∉ C.support → i ≠ j → s i = t) ∧
          (∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n) (L.offset (h n)) ≤
            FixedMinimum.relativeValue t s (p n) (h n) (c n)) := by
    rcases C.successor with hlast | ⟨γ, hγ, hE, hcomp⟩
    · exact Or.inl hlast
    · refine Or.inr ⟨γ, hγ, hE, ?_⟩
      intro j hj
      obtain ⟨J, hJ, hc, hs⟩ := hcomp j hj
      exact ⟨J.slope, fun n => J.offset (h n), hc.comp hhGT, hs,
        fun n => active_relativeValue_le (ha n) hJ⟩
  have hcoord := FixedMinimum.fixed_minimum_label_bound hh hh0 hpcoord
    hm.1 hm.2 C.threshold_gt C.error_pos C.slope_in C.slope_out hoffset hbase
    (C.inner_bound h p p₀ hh hh0 hp hcube ha) hnext
  rw [pi_norm_lt_iff C.error_pos]
  intro i
  exact hcoord i

theorem normalized_shifted_offset {c : ℝ → ℝ} {β : ℝ}
    (hc : c =o[𝓝[>] 0] (fun h : ℝ => h ^ β)) :
    Tendsto (fun h : ℝ => (-h ^ β + c h) / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hlim : Tendsto (fun h : ℝ => -1 + c h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hc.tendsto_div_nhds_zero :
        Tendsto (fun h : ℝ => -1 + c h / h ^ β) (𝓝[>] 0) (𝓝 (-1 + 0)))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
  simp only [add_div, neg_div, div_self hne]

/-- A normalized type offset decays faster than every smaller power. -/
theorem offset_isLittleO_of_normalized {c : ℝ → ℝ} {s β : ℝ}
    (hc : Tendsto (fun h : ℝ => c h / h ^ β) (𝓝[>] 0) (𝓝 (-1)))
    (hsβ : s < β) : c =o[𝓝[>] 0] (fun h : ℝ => h ^ s) := by
  have hi : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hpow := hi.rpow_const_nhds_zero (sub_pos.mpr hsβ)
  have hratio : Tendsto (fun h : ℝ => h ^ β / h ^ s) (𝓝[>] 0) (𝓝 0) := by
    apply hpow.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh β s
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with h hh hz
    exact False.elim ((ne_of_gt (Real.rpow_pos_of_pos hh s)) hz)
  · have hlim : Tendsto (fun h : ℝ => (c h / h ^ β) * (h ^ β / h ^ s))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hc.mul hratio
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hh β)]

/-- Finitely many type certificates have one common exponent strictly above
the fixed minimum at which all their offsets are little-o. This decay allows
localization and inter-family gluing. -/
theorem exists_common_offset_decay {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    ∃ s : ℝ, t < s ∧ ∀ L ∈ Λ, L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ s) := by
  classical
  let β : {L // L ∈ Λ} → ℝ := fun L => (hcert L.1 L.2).threshold
  obtain ⟨s, hts, _, hs⟩ := exists_threshold Finset.univ (fun L => β L - t)
    (fun L _ => sub_pos.mpr (hcert L.1 L.2).threshold_gt)
    (show t < t + 1 by linarith)
  refine ⟨s, hts, ?_⟩
  intro L hL
  have hsβ : s < (hcert L hL).threshold := by
    have h := hs ⟨L, hL⟩ (Finset.mem_univ _)
    dsimp [β] at h
    linarith
  rcases (hcert L hL).offset_behavior with ⟨_, hc⟩ | hc
  · have hc0 : L.offset = fun _ => 0 := funext hc
    rw [hc0]
    exact Asymptotics.isLittleO_zero _ _
  · exact offset_isLittleO_of_normalized hc hsβ

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Filter Topology

namespace Problem326.Affine

theorem localCertificate_of_label_certificates {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hbaseline : constantLabel d t ∈ Λ)
    (hslopes : ∀ L ∈ Λ, Cube t b L.slope)
    (hminima : ∀ L ∈ Λ, HasMinimum L.slope t)
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    Nonempty (LocalCertificate d a b t E) := by
  obtain ⟨η, hη, hoff⟩ := exists_common_offset_decay hcert
  exact ⟨{
    labels := Λ
    baseline := hbaseline
    slopes := hslopes
    minima := hminima
    decayExponent := η
    decay_gt := hη
    offsets := hoff
    approximation := approximatesAtMinimum_of_certificates hbaseline hcert
  }⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Problem326.Affine

local instance {d : ℕ} : DecidableEq (Label d) := Classical.decEq _

/-- Extend coordinates along an injection, using the constant baseline on its complement. -/
def embedCoordinates {k d : ℕ} (e : Fin k ↪ Fin d) (t : ℝ)
    (s : Fin k → ℝ) : Fin d → ℝ :=
  fun i => t + ∑ j, if e j = i then s j - t else 0

@[simp] theorem embedCoordinates_apply {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (s : Fin k → ℝ) (j : Fin k) :
    embedCoordinates e t s (e j) = s j := by
  classical
  simp only [embedCoordinates, e.injective.eq_iff]
  simp

theorem embedCoordinates_outside {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (s : Fin k → ℝ) {i : Fin d} (hi : i ∉ Set.range e) :
    embedCoordinates e t s i = t := by
  classical
  have hne (j : Fin k) : e j ≠ i := fun h => hi ⟨j, h⟩
  simp [embedCoordinates, hne]

/-- The larger-dimensional label used for a fixed-minimum type. -/
def Label.embed {k d : ℕ} (e : Fin k ↪ Fin d) (t β : ℝ)
    (L : Label k) : Label d where
  slope := embedCoordinates e t L.slope
  offset := fun h => -h ^ β + L.offset h

theorem embedCoordinates_dot {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (s : Fin k → ℝ) (x : Fin d → ℝ) :
    (∑ i, embedCoordinates e t s i * x i) =
      (∑ j, s j * x (e j)) + t * ((∑ i, x i) - ∑ j, x (e j)) := by
  classical
  simp only [embedCoordinates, add_mul, Finset.sum_add_distrib]
  have hex : (∑ i : Fin d, (∑ j : Fin k, if e j = i then s j - t else 0) * x i) =
      ∑ j : Fin k, (s j - t) * x (e j) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ite_mul]
  rw [hex]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Embedded affine values differ from their projected values by a common term. -/
theorem Label.embed_value {k d : ℕ} (e : Fin k ↪ Fin d) (t β h : ℝ)
    (L : Label k) (x : Fin d → ℝ) :
    (L.embed e t β).value h x = L.value h (fun j => x (e j)) +
      t * ((∑ i, x i) - ∑ j, x (e j)) - h ^ β := by
  dsimp [Label.value, Label.embed]
  rw [embedCoordinates_dot]
  ring

theorem Label.embed_injective {k d : ℕ} (e : Fin k ↪ Fin d) (t β : ℝ) :
    Function.Injective (Label.embed e t β) := by
  intro L J heq
  have hs : L.slope = J.slope := by
    funext j
    have hj := congrArg (fun Q : Label d => Q.slope (e j)) heq
    simpa only [Label.embed, embedCoordinates_apply] using hj
  have hc : L.offset = J.offset := by
    funext h
    have hh := congrArg (fun Q : Label d => Q.offset h) heq
    dsimp [Label.embed] at hh
    linarith
  cases L
  cases J
  cases hs
  cases hc
  rfl

/-- Common baseline and offset terms preserve all comparisons, including ties. -/
theorem active_embed_iff {k d : ℕ} (e : Fin k ↪ Fin d) (t β h : ℝ)
    (Λ : Finset (Label k)) (L : Label k) (x : Fin d → ℝ) :
    Active (Λ.image (Label.embed e t β)) (L.embed e t β) h x ↔
      Active Λ L h (fun j => x (e j)) := by
  classical
  constructor
  · intro ha
    obtain ⟨J, hJ, hJL⟩ := Finset.mem_image.1 ha.1
    have hJL' : J = L := Label.embed_injective e t β hJL
    subst J
    refine ⟨hJ, ?_⟩
    intro J hJ
    have hh := ha.2 (J.embed e t β) (Finset.mem_image_of_mem _ hJ)
    simp only [Label.embed_value] at hh
    linarith
  · intro ha
    refine ⟨Finset.mem_image_of_mem _ ha.1, ?_⟩
    intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hJ
    have hh := ha.2 Q hQ
    simp only [Label.embed_value]
    linarith

theorem cube_embedCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    {a t β b : ℝ} {s : Fin k → ℝ}
    (hat : a ≤ t) (htβ : t ≤ β) (htb : t ≤ b) (hs : Cube β b s) :
    Cube a b (embedCoordinates e t s) := by
  intro i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    rw [embedCoordinates_apply]
    exact ⟨hat.trans (htβ.trans (hs j).1), (hs j).2⟩
  · rw [embedCoordinates_outside e t s hi]
    exact ⟨hat, htb⟩

theorem hasMinimum_embedCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    (hkd : k < d) {t : ℝ} {s : Fin k → ℝ} (hs : ∀ j, t ≤ s j) :
    HasMinimum (embedCoordinates e t s) t := by
  constructor
  · intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      simpa only [embedCoordinates_apply] using hs j
    · rw [embedCoordinates_outside e t s hi]
  · have hns : ¬ Function.Surjective e := by
      intro hsurj
      have hcard := Fintype.card_le_of_surjective e hsurj
      simp only [Fintype.card_fin] at hcard
      omega
    change ¬ ∀ i, ∃ j, e j = i at hns
    push Not at hns
    obtain ⟨i, hi⟩ := hns
    refine ⟨i, embedCoordinates_outside e t s ?_⟩
    simpa only [Set.mem_range, not_exists] using hi

/-- The raised coordinates of the embedded slope are exactly the injected coordinates. -/
theorem embedCoordinates_gt_baseline_iff {k d : ℕ} (e : Fin k ↪ Fin d)
    {t : ℝ} {s : Fin k → ℝ} (hs : ∀ j, t < s j) (i : Fin d) :
    t < embedCoordinates e t s i ↔ i ∈ Set.range e := by
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    exact iff_of_true (by simpa only [embedCoordinates_apply] using hs j) ⟨j, rfl⟩
  · rw [embedCoordinates_outside e t s hi]
    simp [hi]

theorem tendsto_project_coordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    {p : ℕ → (Fin d → ℝ)} {p₀ : Fin d → ℝ}
    (hp : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun n j => p n (e j)) atTop (𝓝 (fun j => p₀ (e j))) := by
  exact tendsto_pi_nhds.2 (fun j => (tendsto_pi_nhds.1 hp) (e j))

theorem powerPoint_project {k d : ℕ} (e : Fin k ↪ Fin d)
    (h : ℝ) (p : Fin d → ℝ) :
    (fun j => powerPoint h p (e j)) = powerPoint h (fun j => p (e j)) := rfl

/-- Activity in any larger family restricts to the projected lower-dimensional family. -/
theorem active_project_of_active {k d : ℕ} (e : Fin k ↪ Fin d) (t β h : ℝ)
    {Λ : Finset (Label k)} {Γ : Finset (Label d)} {L : Label k}
    (hΛ : Λ.image (Label.embed e t β) ⊆ Γ) (hL : L ∈ Λ)
    (p : Fin d → ℝ)
    (ha : Active Γ (L.embed e t β) h (powerPoint h p)) :
    Active Λ L h (powerPoint h (fun j => p (e j))) := by
  have ha' := active_mono hΛ (Finset.mem_image_of_mem _ hL) ha
  have hp := (active_embed_iff e t β h Λ L (powerPoint h p)).1 ha'
  simpa only [powerPoint_project] using hp

/-- A projected norm estimate controls every raised coordinate of the larger slope. -/
theorem embedded_error_on_range {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) {s : Fin k → ℝ} {p : Fin d → ℝ} {ε : ℝ}
    (herr : ‖(fun j => p (e j)) - s‖ < ε) :
    ∀ i ∈ Set.range e, |p i - embedCoordinates e t s i| < ε := by
  have hε : 0 < ε := (norm_nonneg _).trans_lt herr
  have hh := (pi_norm_lt_iff hε).1 herr
  intro i hi
  obtain ⟨j, rfl⟩ := hi
  simpa only [embedCoordinates_apply, Pi.sub_apply, Real.norm_eq_abs] using hh j

/-- Canonical coordinate injection for a finite support, built from its finite enumeration. -/
def supportEmbedding {d : ℕ} (U : Finset (Fin d)) : Fin U.card ↪ Fin d :=
  U.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ U))

@[simp] theorem supportEmbedding_mem {d : ℕ} (U : Finset (Fin d)) (j : Fin U.card) :
    supportEmbedding U j ∈ U :=
  (U.equivFin.symm j).property

theorem range_supportEmbedding {d : ℕ} (U : Finset (Fin d)) :
    Set.range (supportEmbedding U) = (U : Set (Fin d)) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact supportEmbedding_mem U j
  · intro hi
    refine ⟨U.equivFin ⟨i, hi⟩, ?_⟩
    simp [supportEmbedding]

/-- Every member of an embedded nonempty family has the required baseline minimum. -/
theorem embedded_family_data {k d : ℕ} (e : Fin k ↪ Fin d)
    (hkd : k < d) {a t β b : ℝ}
    (hat : a ≤ t) (htβ : t < β) (hβb : β < b)
    (Λ : Finset (Label k)) (hne : Λ.Nonempty)
    (hslopes : ∀ L ∈ Λ, Cube β b L.slope) :
    (Λ.image (Label.embed e t β)).Nonempty ∧
      ∀ J ∈ Λ.image (Label.embed e t β),
        Cube a b J.slope ∧ HasMinimum J.slope t ∧
        ∀ i, t < J.slope i ↔ i ∈ Set.range e := by
  classical
  refine ⟨hne.image _, ?_⟩
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hJ
  refine ⟨cube_embedCoordinates e hat htβ.le (htβ.trans hβb).le (hslopes L hL), ?_, ?_⟩
  · exact hasMinimum_embedCoordinates e hkd (fun j => htβ.le.trans (hslopes L hL j).1)
  · exact embedCoordinates_gt_baseline_iff e (fun j => htβ.trans_le (hslopes L hL j).1)

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Problem326.Affine

local instance {d : ℕ} : DecidableEq (Label d) := Classical.decEq _

/-- The type-`k` family is the finite union over coordinate injections. Indexing by all
injections avoids dependent coordinate casts; every `k`-element support is represented. -/
def typeFamily {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) : Finset (Label d) :=
  Finset.univ.biUnion (fun e => (Λ e).image (Label.embed e t β))

theorem mem_typeFamily {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) (J : Label d) :
    J ∈ typeFamily t β Λ ↔
      ∃ e : Fin k ↪ Fin d, ∃ L ∈ Λ e, L.embed e t β = J := by
  classical
  simp only [typeFamily, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]

theorem embeddedFamily_subset_typeFamily {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) (e : Fin k ↪ Fin d) :
    (Λ e).image (Label.embed e t β) ⊆ typeFamily t β Λ := by
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hJ
  exact (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩

theorem typeFamily_nonempty {k d : ℕ} (hkd : k ≤ d) (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hne : ∀ e, (Λ e).Nonempty) : (typeFamily t β Λ).Nonempty := by
  let e : Fin k ↪ Fin d := Fin.castLEEmb hkd
  obtain ⟨L, hL⟩ := hne e
  exact ⟨L.embed e t β, (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩⟩

/-- Every member of a type family has baseline minimum and exactly the injected raised support. -/
theorem typeFamily_member_data {k d : ℕ} (hkd : k < d)
    {a t β b : ℝ} (hat : a ≤ t) (htβ : t < β) (hβb : β < b)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hslopes : ∀ e L, L ∈ Λ e → Cube β b L.slope)
    {J : Label d} (hJ : J ∈ typeFamily t β Λ) :
    Cube a b J.slope ∧ HasMinimum J.slope t ∧
      ∃ e : Fin k ↪ Fin d, ∀ i, t < J.slope i ↔ i ∈ Set.range e := by
  obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β Λ J).1 hJ
  refine ⟨cube_embedCoordinates e hat htβ.le (htβ.trans hβb).le (hslopes e L hL),
    hasMinimum_embedCoordinates e hkd (fun j => htβ.le.trans (hslopes e L hL j).1), e, ?_⟩
  exact embedCoordinates_gt_baseline_iff e (fun j => htβ.trans_le (hslopes e L hL j).1)

/-- Every prescribed support of size `k` occurs in the type family. -/
theorem typeFamily_support_exists {k d : ℕ} {t β b : ℝ} (htβ : t < β)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hne : ∀ e, (Λ e).Nonempty)
    (hslopes : ∀ e L, L ∈ Λ e → Cube β b L.slope)
    (U : Finset (Fin d)) (hU : U.card = k) :
    ∃ J ∈ typeFamily t β Λ, ∀ i, t < J.slope i ↔ i ∈ U := by
  let e : Fin k ↪ Fin d := (U.orderEmbOfFin hU).toEmbedding
  obtain ⟨L, hL⟩ := hne e
  refine ⟨L.embed e t β, (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩, ?_⟩
  intro i
  change t < embedCoordinates e t L.slope i ↔ i ∈ U
  rw [embedCoordinates_gt_baseline_iff e (fun j => htβ.trans_le (hslopes e L hL j).1)]
  have hrange : Set.range e = (U : Set (Fin d)) := Finset.range_orderEmbOfFin U hU
  rw [hrange]
  rfl

/-- All comparisons in the total type family imply the lower-dimensional activity hypothesis. -/
theorem typeFamily_active_project {k d : ℕ} (t β h : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (e : Fin k ↪ Fin d) {L : Label k} (hL : L ∈ Λ e)
    (p : Fin d → ℝ)
    (ha : Active (typeFamily t β Λ) (L.embed e t β) h (powerPoint h p)) :
    Active (Λ e) L h (powerPoint h (fun j => p (e j))) :=
  active_project_of_active e t β h (embeddedFamily_subset_typeFamily t β Λ e) hL p ha

/-- The support data in finite-set form, matching the layer-certificate interface. -/
theorem typeFamily_support_data {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k)) {b : ℝ}
    (hslopes : ∀ e L, L ∈ Λ e → Cube β b L.slope)
    {J : Label d} (hJ : J ∈ typeFamily t β Λ) :
    ∃ U : Finset (Fin d), U.card = k ∧
      (∀ i ∈ U, β ≤ J.slope i ∧ J.slope i ≤ b) ∧
      (∀ i ∉ U, J.slope i = t) := by
  classical
  obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β Λ J).1 hJ
  refine ⟨Finset.univ.map e, by simp, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    simpa only [Label.embed, embedCoordinates_apply] using hslopes e L hL j
  · intro i hi
    apply embedCoordinates_outside e t L.slope
    rintro ⟨j, rfl⟩
    exact hi (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)

/-- Every support has a competitor equal to the baseline off that support. -/
theorem typeFamily_supported_competitor {k d : ℕ} (t β : ℝ)
    (Λ : (Fin k ↪ Fin d) → Finset (Label k))
    (hne : ∀ e, (Λ e).Nonempty)
    (U : Finset (Fin d)) (hU : U.card = k) :
    ∃ J ∈ typeFamily t β Λ, ∀ i ∉ U, J.slope i = t := by
  classical
  let e : Fin k ↪ Fin d := (U.orderEmbOfFin hU).toEmbedding
  obtain ⟨L, hL⟩ := hne e
  refine ⟨L.embed e t β, (mem_typeFamily t β Λ _).2 ⟨e, L, hL, rfl⟩, ?_⟩
  intro i hi
  apply embedCoordinates_outside e t L.slope
  have hrange : Set.range e = (U : Set (Fin d)) := Finset.range_orderEmbOfFin U hU
  simpa only [hrange, Finset.mem_coe] using hi

/-- A lower-dimensional little-offset quotient becomes the normalized `-1` offset
required of a positive type. -/
theorem Label.embed_normalized_offset {k d : ℕ} (e : Fin k ↪ Fin d)
    (t β : ℝ) (L : Label k)
    (hL : Tendsto (fun h : ℝ => L.offset h / h ^ β) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => (L.embed e t β).offset h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have heq : (fun h : ℝ => (L.embed e t β).offset h / h ^ β) =ᶠ[𝓝[>] 0]
      (fun h : ℝ => -1 + L.offset h / h ^ β) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change (-h ^ β + L.offset h) / h ^ β = -1 + L.offset h / h ^ β
    rw [add_div, neg_div, div_self (ne_of_gt (Real.rpow_pos_of_pos hh β))]
  have ht : Tendsto (fun h : ℝ => -1 + L.offset h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
    simpa using tendsto_const_nhds.add hL
  exact ht.congr' heq.symm

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326.Affine

/-- Build the finite sequence of type families used at a fixed minimum.
Each new threshold is chosen only after the preceding finite family, so arbitrary
positive label-dependent tolerances are allowed. The family constructor may
itself depend on the chosen threshold. -/
theorem exists_layer_sequence {α : Type uAlpha} (n : ℕ) {t b : ℝ} (htb : t < b)
    (E : α → ℝ) (F₀ : Finset α) (hE₀ : ∀ a ∈ F₀, 0 < E a)
    (Good : ℕ → ℝ → Finset α → Prop)
    (hmake : ∀ k : ℕ, 0 < k → k ≤ n → ∀ β : ℝ, t < β → β < b →
      ∃ F : Finset α, Good k β F ∧ ∀ a ∈ F, 0 < E a) :
    ∃ (β : ℕ → ℝ) (F : ℕ → Finset α),
      β 0 = b ∧ F 0 = F₀ ∧
      (∀ k, t < β k ∧ β k ≤ b ∧ ∀ a ∈ F k, 0 < E a) ∧
      ∀ k < n, β (k + 1) < β k ∧
        (∀ a ∈ F k, β (k + 1) - t < E a) ∧
        Good (k + 1) (β (k + 1)) (F (k + 1)) := by
  classical
  let S := {q : ℝ × Finset α // t < q.1 ∧ q.1 ≤ b ∧ ∀ a ∈ q.2, 0 < E a}
  let s₀ : S := ⟨(b, F₀), htb, le_rfl, hE₀⟩
  have hs : ∀ k : ℕ, ∀ s : S, ∃ s' : S, k < n →
      s'.val.1 < s.val.1 ∧
      (∀ a ∈ s.val.2, s'.val.1 - t < E a) ∧
      Good (k + 1) s'.val.1 s'.val.2 := by
    intro k s
    by_cases hk : k < n
    · obtain ⟨β, htβ, hβupper, hβE⟩ :=
        exists_threshold s.val.2 E s.property.2.2 s.property.1
      have hβb : β < b := hβupper.trans_le s.property.2.1
      obtain ⟨F, hFgood, hFE⟩ := hmake (k + 1) (by omega) (by omega) β htβ hβb
      exact ⟨⟨(β, F), htβ, hβb.le, hFE⟩, fun _ => ⟨hβupper, hβE, hFgood⟩⟩
    · exact ⟨s, fun h => (hk h).elim⟩
  choose next hnext using hs
  let state : ℕ → S := Nat.rec s₀ (fun k s => next k s)
  refine ⟨fun k => (state k).val.1, fun k => (state k).val.2, rfl, rfl, ?_, ?_⟩
  · intro k
    exact (state k).property
  · intro k hk
    exact hnext k (state k) hk

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

open Filter Topology

noncomputable section
namespace Problem326.Affine

/-- The lower-dimensional induction hypothesis, transported to one support. -/
def ApproximatesOnSupport {d : ℕ} (F : Finset (Label d)) (L : Label d)
    (U : Finset (Fin d)) (t b β : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube t b p₀ →
    (∀ i ∈ U, β ≤ p₀ i) →
    (∀ n, Active F L (h n) (powerPoint (h n) (p n))) →
    ∀ i ∈ U, |p₀ i - L.slope i| < E L.slope

/-- Exactly the information needed from one recursively constructed type family.
The zero type is the constant baseline; positive types have normalized offset -1.
No continuity of offsets or tolerances is assumed. -/
structure LayerCertificate {d : ℕ} (t b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (k : ℕ) (β : ℝ) (F : Finset (Label d)) : Prop where
  tolerance_pos : ∀ L ∈ F, 0 < E L.slope
  support_data : ∀ L ∈ F, ∃ U : Finset (Fin d),
    U.card = k ∧
    (∀ i ∈ U, β ≤ L.slope i ∧ L.slope i ≤ b) ∧
    (∀ i ∉ U, L.slope i = t) ∧
    (k = 0 → ∀ h, L.offset h = 0) ∧
    (0 < k → Tendsto (fun h : ℝ => L.offset h / h ^ β)
      (𝓝[>] (0 : ℝ)) (𝓝 (-1))) ∧
    ApproximatesOnSupport F L U t b β E
  supported_competitor : ∀ U : Finset (Fin d), U.card = k →
    ∃ L ∈ F, ∀ i ∉ U, L.slope i = t

def baselineLabel (d : ℕ) (t : ℝ) : Label d := ⟨fun _ => t, fun _ => 0⟩

lemma baseline_layer_certificate {d : ℕ} {t b β : ℝ}
    (E : (Fin d → ℝ) → ℝ) (hE : 0 < E (fun _ => t)) :
    LayerCertificate t b E 0 β {baselineLabel d t} := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    have hL' : L = baselineLabel d t := by simpa using hL
    subst L
    exact hE
  · intro L hL
    have hL' : L = baselineLabel d t := by simpa using hL
    subst L
    refine ⟨∅, rfl, by simp, ?_, ?_, ?_, ?_⟩
    · simp [baselineLabel]
    · simp [baselineLabel]
    · simp
    · intro h p p₀ hh hh0 hp hp₀ hU ha i hi
      simp at hi
  · intro U hU
    have hU' : U = ∅ := Finset.card_eq_zero.mp hU
    refine ⟨baselineLabel d t, by simp, ?_⟩
    simp [baselineLabel]

lemma relativeValue_le_iff {d : ℕ} (t : ℝ) (L J : Label d)
    (h : ℝ) (p : Fin d → ℝ) :
    FixedMinimum.relativeValue t L.slope p h (L.offset h) ≤
      FixedMinimum.relativeValue t J.slope p h (J.offset h) ↔
    L.value h (powerPoint h p) ≤ J.value h (powerPoint h p) := by
  unfold FixedMinimum.relativeValue Label.value powerPoint
  simp only [sub_mul, Finset.sum_sub_distrib]
  constructor <;> intro hle <;> linarith

lemma relativeValue_baseline {d : ℕ} (t h : ℝ) (p : Fin d → ℝ) :
    FixedMinimum.relativeValue t (baselineLabel d t).slope p h
      ((baselineLabel d t).offset h) = 0 := by
  simp [FixedMinimum.relativeValue, baselineLabel]

/-- The union of all types, numbered from zero through `d - 1`. -/
def layerUnion (d : ℕ) (F : ℕ → Finset (Label d)) : Finset (Label d) := by
  classical
  exact (Finset.range d).biUnion F

lemma subset_layerUnion {d k : ℕ} (F : ℕ → Finset (Label d)) (hk : k < d) :
    F k ⊆ layerUnion d F := by
  classical
  intro L hL
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, hL⟩

theorem layerUnion_approximatesAtMinimum {d : ℕ} (hd : 0 < d)
    {a t b : ℝ} (E : (Fin d → ℝ) → ℝ)
    (β : ℕ → ℝ) (F : ℕ → Finset (Label d))
    (hF₀ : F 0 = {baselineLabel d t})
    (hβ : ∀ k < d, t < β k)
    (hcert : ∀ k < d, LayerCertificate t b E k (β k) (F k))
    (hstep : ∀ k, k + 1 < d → β (k + 1) < β k ∧
      ∀ L ∈ F k, β (k + 1) - t < E L.slope) :
    ApproximatesAtMinimum (layerUnion d F) a b t E := by
  classical
  intro L hLall h p p₀ hh hh0 hp hp₀ hm ha
  obtain ⟨k, hk, hL⟩ := Finset.mem_biUnion.mp hLall
  have hkd : k < d := Finset.mem_range.mp hk
  have hc := hcert k hkd
  obtain ⟨U, hUcard, hUin, hUout, hzero, hoffset, hind⟩ := hc.support_data L hL
  have hε : 0 < E L.slope := hc.tolerance_pos L hL
  have hhwithin : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh0, Filter.Eventually.of_forall hh⟩
  have hbaseMem : baselineLabel d t ∈ layerUnion d F := by
    apply subset_layerUnion F hd
    rw [hF₀]
    simp
  have hbase : ∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n) (L.offset (h n)) ≤ 0 := by
    intro n
    have hv := (ha n).2 (baselineLabel d t) hbaseMem
    have hr := (relativeValue_le_iff t L (baselineLabel d t) (h n) (p n)).mpr hv
    simpa only [relativeValue_baseline] using hr
  have hOff : (U = ∅ ∧ ∀ n, L.offset (h n) = 0) ∨
      Tendsto (fun n => L.offset (h n) / h n ^ β k) atTop (𝓝 (-1)) := by
    by_cases hk0 : k = 0
    · exact Or.inl ⟨Finset.card_eq_zero.mp (hUcard.trans hk0), fun n => hzero hk0 (h n)⟩
    · exact Or.inr ((hoffset (Nat.pos_of_ne_zero hk0)).comp hhwithin)
  have hInd : (∀ i ∈ U, β k ≤ p₀ i) →
      ∀ i ∈ U, |p₀ i - L.slope i| < E L.slope := by
    intro hraised
    apply hind h p p₀ hh hh0 hp (fun i => ⟨hm.1 i, (hp₀ i).2⟩) hraised
    intro n
    exact active_mono (subset_layerUnion F hkd) hL (ha n)
  have hNext : (∀ i ∉ U, ∀ j ∉ U, i = j) ∨
      ∃ γ : ℝ, γ < β k ∧ γ - t < E L.slope ∧
        ∀ j, j ∉ U → ∃ s : Fin d → ℝ, ∃ c : ℕ → ℝ,
          Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 (-1)) ∧
          (∀ i, i ∉ U → i ≠ j → s i = t) ∧
          (∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n) (L.offset (h n)) ≤
            FixedMinimum.relativeValue t s (p n) (h n) (c n)) := by
    by_cases hkNext : k + 1 < d
    · right
      refine ⟨β (k + 1), (hstep k hkNext).1, (hstep k hkNext).2 L hL, ?_⟩
      intro j hj
      have hC := hcert (k + 1) hkNext
      obtain ⟨J, hJ, hJout⟩ := hC.supported_competitor (insert j U) (by simp [hj, hUcard])
      obtain ⟨V, hVcard, hVin, hVout, hVzero, hVoffset, hVind⟩ := hC.support_data J hJ
      refine ⟨J.slope, fun n => J.offset (h n), (hVoffset (by omega)).comp hhwithin, ?_, ?_⟩
      · intro i hi hij
        apply hJout i
        simp [hi, hij]
      · intro n
        apply (relativeValue_le_iff t L J (h n) (p n)).mpr
        exact (ha n).2 J (subset_layerUnion F hkNext hJ)
    · left
      have hcard : (Finset.univ \ U).card ≤ 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]
        simp only [Finset.card_univ, Fintype.card_fin, hUcard]
        omega
      intro i hi j hj
      exact (Finset.card_le_one.mp hcard) i (by simp [hi]) j (by simp [hj])
  have hbound := FixedMinimum.fixed_minimum_label_bound hh hh0
    (fun i => (tendsto_pi_nhds.mp hp) i) hm.1 hm.2 (hβ k hkd) hε
    (fun i hi => (hUin i hi).1) hUout hOff hbase hInd hNext
  apply (pi_norm_lt_iff hε).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hbound i

/-- A normalized leading power is negligible relative to each strictly lower
power. This yields the stronger local offset decay, not merely decay at `t`. -/
lemma offset_isLittleO_of_normalized_limit {c : ℝ → ℝ} {β q A : ℝ}
    (hqβ : q < β)
    (hc : Tendsto (fun h : ℝ => c h / h ^ β) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) c (fun h : ℝ => h ^ q) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousWithinAt_id
  have hpow : Tendsto (fun h : ℝ => h ^ β / h ^ q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlim := hid.rpow_const_nhds_zero (sub_pos.mpr hqβ)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh β q
  have hlim := hc.mul hpow
  simp only [mul_zero] at hlim
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
    field_simp [hne]
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun hzero => (ne_of_gt (Real.rpow_pos_of_pos hh q) hzero).elim

/-- The actual finite dependent construction at one fixed minimum, separated
from the lower-dimensional embedding used to produce each positive-type layer.
The returned decay has a strictly higher exponent than `t`, allowing localization. -/
theorem exists_fixed_minimum_family_of_layers {d : ℕ} (hd : 0 < d)
    {a t b : ℝ} (htb : t < b) (E : (Fin d → ℝ) → ℝ)
    (hE₀ : 0 < E (fun _ => t))
    (hmake : ∀ k : ℕ, 0 < k → k < d → ∀ β : ℝ, t < β → β < b →
      ∃ F : Finset (Label d), LayerCertificate t b E k β F) :
    ∃ Λ : Finset (Label d), baselineLabel d t ∈ Λ ∧
      ApproximatesAtMinimum Λ a b t E ∧
      ∀ L ∈ Λ, Cube t b L.slope ∧ HasMinimum L.slope t ∧
        ∃ q : ℝ, t < q ∧
          Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) L.offset (fun h : ℝ => h ^ q) := by
  classical
  obtain ⟨β, F, hβ₀, hF₀, hvalid, hnext⟩ :=
    exists_layer_sequence (d - 1) htb (fun L : Label d => E L.slope)
      {baselineLabel d t}
      (by intro L hL; have hL' : L = baselineLabel d t := by simpa using hL
          subst L; exact hE₀)
      (fun k β F => LayerCertificate t b E k β F)
      (by
        intro k hk hkd β htβ hβb
        obtain ⟨F, hF⟩ := hmake k hk (by omega) β htβ hβb
        exact ⟨F, hF, hF.tolerance_pos⟩)
  have hcert : ∀ k < d, LayerCertificate t b E k (β k) (F k) := by
    intro k hkd
    by_cases hk0 : k = 0
    · subst k
      rw [hF₀]
      exact baseline_layer_certificate E hE₀
    · have hkpred : k - 1 < d - 1 := by omega
      have hgood := (hnext (k - 1) hkpred).2.2
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] using hgood
  have hstep : ∀ k, k + 1 < d → β (k + 1) < β k ∧
      ∀ L ∈ F k, β (k + 1) - t < E L.slope := by
    intro k hk
    exact ⟨(hnext k (by omega)).1, (hnext k (by omega)).2.1⟩
  refine ⟨layerUnion d F, ?_, ?_, ?_⟩
  · apply subset_layerUnion F hd
    rw [hF₀]
    simp
  · exact layerUnion_approximatesAtMinimum hd E β F hF₀
      (fun k _ => (hvalid k).1) hcert hstep
  · intro L hLall
    obtain ⟨k, hk, hL⟩ := Finset.mem_biUnion.mp hLall
    have hkd : k < d := Finset.mem_range.mp hk
    obtain ⟨U, hUcard, hUin, hUout, hzero, hoffset, hind⟩ :=
      (hcert k hkd).support_data L hL
    have hlow : ∀ i, t ≤ L.slope i := by
      intro i
      by_cases hi : i ∈ U
      · exact (hvalid k).1.le.trans (hUin i hi).1
      · rw [hUout i hi]
    have hcube : Cube t b L.slope := by
      intro i
      refine ⟨hlow i, ?_⟩
      by_cases hi : i ∈ U
      · exact (hUin i hi).2
      · rw [hUout i hi]
        exact htb.le
    have hnotall : ¬ ∀ i, i ∈ U := by
      intro hall
      have hUuniv : U = Finset.univ := Finset.eq_univ_of_forall hall
      rw [hUuniv, Finset.card_univ, Fintype.card_fin] at hUcard
      omega
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    refine ⟨hcube, ⟨hlow, i, hUout i hi⟩, ?_⟩
    let q := (t + β k) / 2
    have htq : t < q := by dsimp [q]; linarith [(hvalid k).1]
    have hqβ : q < β k := by dsimp [q]; linarith [(hvalid k).1]
    refine ⟨q, htq, ?_⟩
    by_cases hk0 : k = 0
    · have hz : L.offset = fun _ => 0 := funext (hzero hk0)
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
    · exact offset_isLittleO_of_normalized_limit hqβ (hoffset (Nat.pos_of_ne_zero hk0))

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
open Filter Topology

namespace Problem326.Affine

local instance {d : ℕ} : DecidableEq (Label d) := Classical.decEq _

/-- Project the full lower-dimensional approximation certificate into a member of the
injection-indexed type family. The approximating exponents need not stay in any cube. -/
theorem typeFamily_approximatesOnSupport {k d : ℕ} (t β b : ℝ)
    (E : (Fin d → ℝ) → ℝ)
    (C : ∀ e : Fin k ↪ Fin d,
      FullCertificate k β b (fun s => E (embedCoordinates e t s)))
    (e : Fin k ↪ Fin d) {L : Label k} (hL : L ∈ (C e).labels) :
    ApproximatesOnSupport
      (typeFamily t β (fun e => (C e).labels)) (L.embed e t β)
      (Finset.univ.map e) t b β E := by
  intro h p p₀ hh hh0 hp hp₀ hraised ha
  have hpProj : Cube β b (fun j => p₀ (e j)) := by
    intro j
    exact ⟨hraised (e j) (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩), (hp₀ (e j)).2⟩
  have hlocal : ∀ n, Active (C e).labels L (h n)
      (powerPoint (h n) (fun j => p n (e j))) := by
    intro n
    exact typeFamily_active_project t β (h n) (fun e => (C e).labels) e hL (p n) (ha n)
  have herr := (C e).approximation L hL h (fun n j => p n (e j))
    (fun j => p₀ (e j)) hh hh0 (tendsto_project_coordinates e hp) hpProj hlocal
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
  exact embedded_error_on_range e t herr (e j) ⟨j, rfl⟩

/-- The actual positive-type constructor: lower-dimensional full certificates for every
coordinate injection produce the exact layer certificate consumed by fixed-minimum assembly. -/
theorem typeFamily_layerCertificate {k d : ℕ} (hk : 0 < k)
    {t β b : ℝ} (htβ : t < β) (hβb : β < b)
    (E : (Fin d → ℝ) → ℝ)
    (hE : ∀ r, Cube t b r → 0 < E r)
    (C : ∀ e : Fin k ↪ Fin d,
      FullCertificate k β b (fun s => E (embedCoordinates e t s))) :
    LayerCertificate t b E k β (typeFamily t β (fun e => (C e).labels)) := by
  classical
  constructor
  · intro J hJ
    obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β (fun e => (C e).labels) J).1 hJ
    apply hE
    exact cube_embedCoordinates e le_rfl htβ.le (htβ.trans hβb).le ((C e).slopes L hL)
  · intro J hJ
    obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β (fun e => (C e).labels) J).1 hJ
    refine ⟨Finset.univ.map e, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      simpa only [Label.embed, embedCoordinates_apply] using (C e).slopes L hL j
    · intro i hi
      apply embedCoordinates_outside e t L.slope
      rintro ⟨j, rfl⟩
      exact hi (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)
    · intro hk0
      omega
    · intro _
      exact Label.embed_normalized_offset e t β L
        ((C e).offsets L hL).tendsto_div_nhds_zero
    · exact typeFamily_approximatesOnSupport t β b E C e hL
  · exact typeFamily_supported_competitor t β (fun e => (C e).labels)
      (fun e => (C e).nonempty)

/-- The per-layer existence interface used by the finite threshold recursion.
The only input is the lower-dimensional full approximation theorem. -/
theorem exists_typeFamily_layerCertificate {k d : ℕ}
    (hk : 0 < k) (hkd : k < d) {t β b : ℝ}
    (htβ : t < β) (hβb : β < b)
    (E : (Fin d → ℝ) → ℝ)
    (hE : ∀ r, Cube t b r → 0 < E r)
    (hIH : ∀ E' : (Fin k → ℝ) → ℝ,
      (∀ s, Cube β b s → 0 < E' s) → Nonempty (FullCertificate k β b E')) :
    ∃ F : Finset (Label d), F.Nonempty ∧ LayerCertificate t b E k β F := by
  classical
  have hC (e : Fin k ↪ Fin d) :
      Nonempty (FullCertificate k β b (fun s => E (embedCoordinates e t s))) := by
    apply hIH
    intro s hs
    exact hE _ (cube_embedCoordinates e le_rfl htβ.le (htβ.trans hβb).le hs)
  let C (e : Fin k ↪ Fin d) := Classical.choice (hC e)
  exact ⟨typeFamily t β (fun e => (C e).labels),
    typeFamily_nonempty hkd.le t β _ (fun e => (C e).nonempty),
    typeFamily_layerCertificate hk htβ hβb E hE C⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

open Filter Topology

noncomputable section
namespace Problem326.Affine

/-- Turn the output of the finite layer construction into the canonical local
certificate. The finite family admits one common stronger decay exponent. -/
theorem localCertificate_of_layers {d : ℕ} (hd : 0 < d)
    {a t b : ℝ} (htb : t < b) (E : (Fin d → ℝ) → ℝ)
    (hE₀ : 0 < E (fun _ => t))
    (hmake : ∀ k : ℕ, 0 < k → k < d → ∀ β : ℝ, t < β → β < b →
      ∃ F : Finset (Label d), LayerCertificate t b E k β F) :
    Nonempty (LocalCertificate d a b t E) := by
  classical
  obtain ⟨Λ, hbase, happrox, hdata⟩ :=
    exists_fixed_minimum_family_of_layers (a := a) hd htb E hE₀ hmake
  have hdecay : ∀ L : Λ, ∃ q : ℝ, t < q ∧
      Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) L.val.offset (fun h : ℝ => h ^ q) := by
    intro L
    exact (hdata L.val L.property).2.2
  choose q hqt hqdec using hdecay
  obtain ⟨η, htη, hηupper, hηq⟩ := exists_threshold (Finset.univ : Finset Λ)
    (fun L => q L - t) (fun L _ => sub_pos.mpr (hqt L))
    (show t < t + 1 by linarith)
  refine ⟨{
    labels := Λ
    baseline := hbase
    slopes := fun L hL => (hdata L hL).1
    minima := fun L hL => (hdata L hL).2.1
    decayExponent := η
    decay_gt := htη
    offsets := ?_
    approximation := happrox
  }⟩
  intro L hL
  let J : Λ := ⟨L, hL⟩
  have hηqJ : η < q J := by
    have hbound := hηq J (Finset.mem_univ J)
    linarith
  exact offset_isLittleO_of_normalized_limit hηqJ (hqdec J).tendsto_div_nhds_zero

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


open Set Filter
open scoped Topology

namespace Problem326

/-- Limiting points of activity as the positive parameter tends to zero,
expressed using closed sets; no continuity of `active` is required. -/
def activityLimitSet {X : Type uX} [TopologicalSpace X]
    (active : ℝ → X → Prop) : Set X :=
  ⋂ n : ℕ, closure {p | ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧ active h p}

theorem isClosed_activityLimitSet {X : Type uX} [TopologicalSpace X]
    (active : ℝ → X → Prop) : IsClosed (activityLimitSet active) :=
  isClosed_iInter (fun _ => isClosed_closure)

/-- Every limit of active points at positive parameters tending to zero
belongs to the closed activity-limit set. -/
theorem mem_activityLimitSet_of_tendsto
    {X : Type uX} [TopologicalSpace X] {active : ℝ → X → Prop}
    {h : ℕ → ℝ} {p : ℕ → X} {z : X}
    (hhpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 z)) (ha : ∀ n, active (h n) (p n)) :
    z ∈ activityLimitSet active := by
  apply mem_iInter.mpr
  intro n
  apply isClosed_closure.mem_of_tendsto hp
  have hev : ∀ᶠ k in atTop, h k < 1 / ((n : ℝ) + 1) :=
    hh.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hev] with k hk
  exact subset_closure ⟨h k, hhpos k, hk, ha k⟩

/-- In a pseudometric space every point of the activity-limit set is realized
by an actual sequence, even when activity is not a closed relation. -/
theorem exists_active_sequence_of_mem_activityLimitSet
    {X : Type uX} [PseudoMetricSpace X] {active : ℝ → X → Prop} {z : X}
    (hz : z ∈ activityLimitSet active) :
    ∃ (h : ℕ → ℝ) (p : ℕ → X), (∀ n, 0 < h n) ∧
      Tendsto h atTop (𝓝 0) ∧ Tendsto p atTop (𝓝 z) ∧
      ∀ n, active (h n) (p n) := by
  classical
  have hex (n : ℕ) : ∃ p, (∃ h : ℝ, 0 < h ∧
      h < 1 / ((n : ℝ) + 1) ∧ active h p) ∧
      dist z p < 1 / ((n : ℝ) + 1) :=
    Metric.mem_closure_iff.mp (mem_iInter.mp hz n)
      (1 / ((n : ℝ) + 1)) (by positivity)
  choose p hp hdist using hex
  choose h hhpos hhsmall ha using hp
  refine ⟨h, p, hhpos, ?_, ?_, ha⟩
  · exact squeeze_zero (fun n => (hhpos n).le) (fun n => (hhsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [dist_comm] using (hdist n).le

/-- Compactness upgrades avoidance of one level to a positive uniform gap. -/
theorem compact_avoid_level_has_uniform_gap
    {X : Type uX} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) (t : ℝ)
    (hne : ∀ x ∈ K, f x ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ |f x - t| := by
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · exact ⟨1, zero_lt_one, by simp [hEmpty]⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hNonempty
      ((hf.sub continuousOn_const).abs)
    exact ⟨|f x - t|, abs_pos.mpr (sub_ne_zero.mpr (hne x hx)), hmin⟩

/-- A good-label guarantee at one level extends to nearby levels. This is the
compact bad-limit-set argument; tolerances may vary arbitrarily between labels. -/
theorem activity_limits_good_near_level
    {X : Type uX} [TopologicalSpace X] {ι : Type uIota} [Finite ι]
    {K : Set X} (hK : IsCompact K) (active : ι → ℝ → X → Prop)
    (good : ι → Set X) (hgood : ∀ i, IsOpen (good i))
    {f : X → ℝ} (hf : ContinuousOn f K) (t : ℝ)
    (hlevel : ∀ i z, z ∈ K → f z = t →
      z ∈ activityLimitSet (active i) → z ∈ good i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ K, |f z - t| < ρ →
      ∀ i, z ∈ activityLimitSet (active i) → z ∈ good i := by
  classical
  let B : Set X := K ∩ ⋃ i, activityLimitSet (active i) ∩ (good i)ᶜ
  have hB : IsCompact B := hK.inter_right
    (isClosed_iUnion_of_finite (fun i =>
      (isClosed_activityLimitSet (active i)).inter (hgood i).isClosed_compl))
  have hne : ∀ z ∈ B, f z ≠ t := by
    intro z hz heq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz.2
    exact hi.2 (hlevel i z hz.1 heq hi.1)
  obtain ⟨ρ, hρ, hgap⟩ := compact_avoid_level_has_uniform_gap hB
    (hf.mono inter_subset_left) t hne
  refine ⟨ρ, hρ, ?_⟩
  intro z hz hnear i ha
  by_contra hbad
  exact (not_le_of_gt hnear) (hgap z ⟨hz, mem_iUnion.mpr ⟨i, ha, hbad⟩⟩)

end Problem326

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326.Affine

/-- The least coordinate in a positive-dimensional exponent vector. -/
def minimumCoordinate {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ p

theorem continuous_minimumCoordinate {d : ℕ} (hd : 0 < d) :
    Continuous (minimumCoordinate hd) := by
  exact Continuous.finset_inf'_apply _ (fun i _ => continuous_apply i)

theorem hasMinimum_minimumCoordinate {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ) :
    HasMinimum p (minimumCoordinate hd p) := by
  refine ⟨fun i => Finset.inf'_le p (Finset.mem_univ i), ?_⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, hd⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin d)).Nonempty) p
  exact ⟨i, heq.symm⟩

theorem minimumCoordinate_eq_of_hasMinimum {d : ℕ} (hd : 0 < d)
    {p : Fin d → ℝ} {t : ℝ} (hm : HasMinimum p t) :
    minimumCoordinate hd p = t := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hm.2
    exact (Finset.inf'_le p (Finset.mem_univ i)).trans_eq hi
  · exact Finset.le_inf' _ p (fun i _ => hm.1 i)

theorem minimumCoordinate_mem_Icc {d : ℕ} (hd : 0 < d)
    {p : Fin d → ℝ} {a b : ℝ} (hp : Cube a b p) :
    minimumCoordinate hd p ∈ Icc a b := by
  obtain ⟨i, hi⟩ := (hasMinimum_minimumCoordinate hd p).2
  simpa only [← hi, Set.mem_Icc] using hp i

theorem isCompact_cube_localBand {d : ℕ} (a b : ℝ) :
    IsCompact {p : Fin d → ℝ | Cube a b p} := by
  exact isCompact_pi_infinite (fun _ => isCompact_Icc)

/-- Approximation at a fixed
minimum level extends to a band of nearby minimum levels. Approximating
sequences themselves may leave the exponent cube. -/
theorem exists_local_band_of_approximatesAtMinimum
    {d : ℕ} (hd : 0 < d) (Λ : Finset (Label d)) (a b t : ℝ)
    (E : (Fin d → ℝ) → ℝ) (happrox : ApproximatesAtMinimum Λ a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ L ∈ Λ,
      ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
      |minimumCoordinate hd p₀ - t| < ρ →
      (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
      ‖p₀ - L.slope‖ < E L.slope := by
  classical
  let active : Λ → ℝ → (Fin d → ℝ) → Prop :=
    fun L h p => Active Λ L.val h (powerPoint h p)
  let good : Λ → Set (Fin d → ℝ) :=
    fun L => {p | ‖p - L.val.slope‖ < E L.val.slope}
  have hgood (L : Λ) : IsOpen (good L) :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  have hlevel (L : Λ) (z : Fin d → ℝ) (hz : Cube a b z)
      (heq : minimumCoordinate hd z = t)
      (ha : z ∈ activityLimitSet (active L)) : z ∈ good L := by
    obtain ⟨h, p, hhpos, hh, hp, hactive⟩ :=
      exists_active_sequence_of_mem_activityLimitSet ha
    apply happrox L.val L.property h p z hhpos hh hp hz
    · simpa only [heq] using hasMinimum_minimumCoordinate hd z
    · exact hactive
  obtain ⟨ρ, hρ, hband⟩ := activity_limits_good_near_level
    (isCompact_cube_localBand (d := d) a b) active good hgood
    (continuous_minimumCoordinate hd).continuousOn t hlevel
  refine ⟨ρ, hρ, ?_⟩
  intro L hL h p p₀ hhpos hh hp hp₀ hnear hactive
  exact hband p₀ hp₀ hnear ⟨L, hL⟩
    (mem_activityLimitSet_of_tendsto hhpos hh hp hactive)

/-- Convenient family-level interface for gluing: the same finite family
approximates at every minimum level in an open interval about `t`. -/
theorem approximatesAtMinimum_nearby
    {d : ℕ} (hd : 0 < d) (Λ : Finset (Label d)) (a b t : ℝ)
    (E : (Fin d → ℝ) → ℝ) (happrox : ApproximatesAtMinimum Λ a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ Ioo (t - ρ) (t + ρ),
      ApproximatesAtMinimum Λ a b s E := by
  obtain ⟨ρ, hρ, hband⟩ :=
    exists_local_band_of_approximatesAtMinimum hd Λ a b t E happrox
  refine ⟨ρ, hρ, ?_⟩
  intro s hs L hL h p p₀ hhpos hh hp hp₀ hm hactive
  apply hband L hL h p p₀ hhpos hh hp hp₀ _ hactive
  rw [minimumCoordinate_eq_of_hasMinimum hd hm, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


open Filter Asymptotics
open scoped Topology

namespace Problem326

private lemma power_isLittleO_at_zero {a b : ℝ} (hab : a < b) :
    (fun h : ℝ => h ^ b) =o[𝓝[>] 0] (fun h => h ^ a) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun he => (ne_of_gt (Real.rpow_pos_of_pos hh a) he).elim
  · have hlim : Tendsto (fun h : ℝ => h ^ (b - a)) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hp := hid.rpow tendsto_const_nhds (Or.inr (sub_pos.mpr hab))
      simpa only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hab))] using hp
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh b a

/-- Finitely many offsets with power decay strictly stronger than `h^t` share
one stronger decay exponent. The individual powers may vary with the label. -/
theorem exists_common_offset_decay {ι : Type uIota} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ → ℝ) (t : ℝ)
    (hc : ∀ i, ∃ β : ℝ, t < β ∧ c i =O[𝓝[>] 0] (fun h => h ^ β)) :
    ∃ η : ℝ, t < η ∧ ∀ i, c i =o[𝓝[>] 0] (fun h => h ^ η) := by
  classical
  choose β hβ hO using hc
  let μ := Finset.univ.inf' Finset.univ_nonempty β
  have htμ : t < μ := (Finset.lt_inf'_iff _).2 fun i _ => hβ i
  let η := (t + μ) / 2
  have htη : t < η := by dsimp [η]; linarith
  have hημ : η < μ := by dsimp [η]; linarith
  refine ⟨η, htη, fun i => ?_⟩
  have hηβ : η < β i := hημ.trans_le (Finset.inf'_le _ (Finset.mem_univ i))
  exact (hO i).trans_isLittleO (power_isLittleO_at_zero hηβ)

/-- A pre-existing localization radius can be shrunk so that all local offsets
are little-o of `h^(t+ρ)`, as required by the affine-family gluing argument. -/
theorem exists_radius_with_offset_decay {ι : Type uIota} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ → ℝ) (t ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hc : ∀ i, ∃ β : ℝ, t < β ∧ c i =O[𝓝[>] 0] (fun h => h ^ β)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧
      ∀ i, c i =o[𝓝[>] 0] (fun h => h ^ (t + ρ)) := by
  obtain ⟨η, htη, hη⟩ := exists_common_offset_decay c t hc
  let ρ := min (ρ₀ / 2) ((η - t) / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ₀' : ρ < ρ₀ := (min_le_left _ _).trans_lt (by linarith)
  have htρη : t + ρ < η := by
    have hle : ρ ≤ (η - t) / 2 := min_le_right _ _
    linarith
  refine ⟨ρ, hρ, hρ₀', fun i => ?_⟩
  exact (hη i).trans (power_isLittleO_at_zero htρη)

/-- The offsets produced by the type construction have the required big-O
bound even though the leading negative power prevents a little-o bound at
that same exponent. -/
theorem shifted_offset_isBigO {d : ℝ → ℝ} {β : ℝ}
    (hd : d =o[𝓝[>] 0] (fun h => h ^ β)) :
    (fun h => -(h ^ β) + d h) =O[𝓝[>] 0] (fun h => h ^ β) := by
  exact (isBigO_refl (fun h : ℝ => h ^ β) (𝓝[>] 0)).neg_left.add hd.isBigO

/-- Normalizing a constructed negative-shift offset by its leading power gives
limit `-1`; this is the exact sequential input used by fixed-minimum activity estimates. -/
theorem shifted_offset_normalized_limit {d : ℝ → ℝ} {β : ℝ}
    (hd : d =o[𝓝[>] 0] (fun h => h ^ β)) :
    Tendsto (fun h : ℝ => (-(h ^ β) + d h) / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hconst : Tendsto (fun _ : ℝ => (-1 : ℝ)) (𝓝[>] 0) (𝓝 (-1)) :=
    tendsto_const_nhds
  have hlim := hconst.add hd.tendsto_div_nhds_zero
  have hlim' : Tendsto (fun h : ℝ => -1 + d h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
  field_simp

end Problem326

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem326.Affine

/-- A fixed-minimum certificate supplies a common neighborhood radius with
both approximation throughout the band and the stronger offset decay used
by the interval-gluing construction. -/
theorem LocalCertificate.exists_radius
    {d : ℕ} (hd : 0 < d) {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (C : LocalCertificate d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ L ∈ C.labels,
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ (t + ρ))) ∧
      ∀ s : ℝ, |s - t| < ρ → ApproximatesAtMinimum C.labels a b s E := by
  classical
  obtain ⟨ρ₀, hρ₀, hnear⟩ := approximatesAtMinimum_nearby
    hd C.labels a b t E C.approximation
  let : Nonempty C.labels := ⟨⟨_, C.baseline⟩⟩
  have hdecay (L : C.labels) : ∃ β : ℝ, t < β ∧
      L.val.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β) :=
    ⟨C.decayExponent, C.decay_gt, (C.offsets L.val L.property).isBigO⟩
  obtain ⟨ρ, hρ, hρsmall, hoffsets⟩ := exists_radius_with_offset_decay
    (fun L : C.labels => L.val.offset) t ρ₀ hρ₀ hdecay
  refine ⟨ρ, hρ, (fun L hL => hoffsets ⟨L, hL⟩), ?_⟩
  intro s hs
  apply hnear s
  have h := abs_lt.mp (hs.trans hρsmall)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.AffineGluing

/-- A positive comparison scale dominates a finite affine error that is little-o of it. -/
theorem eventually_pos_sum_add_scale {α : Type uAlpha} {ι : Type uIota} [Fintype ι]
    {l : Filter α} {x : ι → α → ℝ} {c s : α → ℝ} (a : ι → ℝ)
    (hs : ∀ᶠ n in l, 0 < s n) (hc : c =o[l] s)
    (hx : ∀ i, x i =o[l] s) :
    ∀ᶠ n in l, 0 < (∑ i, a i * x i n) + c n + s n := by
  classical
  have hsum : (fun n => ∑ i, a i * x i n) =o[l] s := by
    exact IsLittleO.fun_sum (fun i _ => (hx i).const_mul_left (a i))
  have herr := (hsum.add hc).eventuallyLT_norm_of_eventually_pos
    (hs.mono fun n hn => by simpa only [Real.norm_eq_abs, abs_of_pos hn] using hn)
  filter_upwards [hs, herr] with n hn he
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn] at he
  have := (abs_lt.mp he).1
  linarith

/-- One positive coordinate contribution that dominates the comparison scale also
    dominates all nonnegative remaining contributions and a little-o offset. -/
theorem eventually_pos_sum_add_sub_scale {α : Type uAlpha} {ι : Type uIota} [Fintype ι]
    {l : Filter α} {x : ι → α → ℝ} {c s : α → ℝ} (a : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 ≤ a i) (haj : 0 < a j)
    (hs : ∀ᶠ n in l, 0 < s n) (hc : c =o[l] s)
    (hx : ∀ᶠ n in l, ∀ i, 0 ≤ x i n)
    (hj : Tendsto (fun n => x j n / s n) l atTop) :
    ∀ᶠ n in l, 0 < (∑ i, a i * x i n) + c n - s n := by
  classical
  have hlarge := hj.eventually_gt_atTop (3 / a j)
  filter_upwards [hs, hc.eventuallyLE, hx, hlarge] with n hn he hx hlarge
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn] at he
  have hcoord : 3 * s n < a j * x j n := by
    have h := (lt_div_iff₀ hn).mp hlarge
    have h' := mul_lt_mul_of_pos_left h haj
    field_simp at h'
    nlinarith
  have hsum : a j * x j n ≤ ∑ i, a i * x i n := by
    exact Finset.single_le_sum (fun i _ => mul_nonneg (ha i) (hx i)) (Finset.mem_univ j)
  have he' := (abs_le.mp he).1
  linarith

/-- The upper comparison in affine gluing forces some limiting exponent below the cut.
    The asymptotic hypotheses are exactly the variable-exponent power estimates. -/
theorem active_upper_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hgap : ∀ i, q < p i → x i =o[atTop] s)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n + s n ≤ 0) :
    ∃ i, p i ≤ q := by
  classical
  by_contra h
  have hp : ∀ i, q < p i := by simpa only [not_exists, not_le] using h
  have hpos := eventually_pos_sum_add_scale a hs hc (fun i => hgap i (hp i))
  obtain ⟨n, hn, hn'⟩ := (hpos.and hactive).exists
  exact (not_lt_of_ge hn') hn

/-- The lower comparison in affine gluing forces every limiting exponent above the cut. -/
theorem active_lower_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (ha : ∀ i, 0 < a i)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hx : ∀ᶠ n in atTop, ∀ i, 0 ≤ x i n)
    (hgap : ∀ i, p i < q → Tendsto (fun n => x i n / s n) atTop atTop)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n - s n ≤ 0) :
    ∀ i, q ≤ p i := by
  intro i
  by_contra hi
  have hpos := eventually_pos_sum_add_sub_scale a i (fun j => (ha j).le)
    (ha i) hs hc hx (hgap i (lt_of_not_ge hi))
  obtain ⟨n, hn, hn'⟩ := (hpos.and hactive).exists
  exact (not_lt_of_ge hn') hn

/-- A supported version of the upper comparison: coordinates with zero coefficient
    need no asymptotic control. This is useful in the fixed-minimum induction. -/
theorem active_upper_cut_on_support {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hgap : ∀ i, a i ≠ 0 → q < p i → x i =o[atTop] s)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n + s n ≤ 0) :
    ∃ i, a i ≠ 0 ∧ p i ≤ q := by
  classical
  by_contra h
  have hp : ∀ i, a i ≠ 0 → q < p i := by
    intro i hi
    exact lt_of_not_ge (fun hpi => h ⟨i, hi, hpi⟩)
  have hterm : ∀ i, (fun n => a i * x i n) =o[atTop] s := by
    intro i
    by_cases hi : a i = 0
    · simpa only [hi, zero_mul] using (isLittleO_zero s atTop)
    · exact (hgap i hi (hp i hi)).const_mul_left (a i)
  have hsum : (fun n => ∑ i, a i * x i n) =o[atTop] s := by
    exact IsLittleO.fun_sum (fun i _ => hterm i)
  have herr := (hsum.add hc).eventuallyLT_norm_of_eventually_pos
    (hs.mono fun n hn => by simpa only [Real.norm_eq_abs, abs_of_pos hn] using hn)
  obtain ⟨n, hn, he, hact⟩ := (hs.and (herr.and hactive)).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn] at he
  have := (abs_lt.mp he).1
  linarith

/-- With nonnegative contributions, only strictly positive coefficients force a
    lower bound on the corresponding limiting exponent. -/
theorem active_nonnegative_lower_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c s : ℕ → ℝ} (a p : ι → ℝ) (q : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hs : ∀ᶠ n in atTop, 0 < s n) (hc : c =o[atTop] s)
    (hx : ∀ᶠ n in atTop, ∀ i, 0 ≤ x i n)
    (hgap : ∀ i, p i < q → Tendsto (fun n => x i n / s n) atTop atTop)
    (hactive : ∀ᶠ n in atTop, (∑ i, a i * x i n) + c n - s n ≤ 0) :
    ∀ i, 0 < a i → q ≤ p i := by
  intro i hi
  by_contra hpi
  have hpos := eventually_pos_sum_add_sub_scale a i ha hi hs hc hx
    (hgap i (lt_of_not_ge hpi))
  obtain ⟨n, hn, hn'⟩ := (hpos.and hactive).exists
  exact (not_lt_of_ge hn') hn

/-- Common offset shifts preserve all comparisons inside a local family. -/
theorem common_shift_comparison (a b shift : ℝ) :
    a - shift ≤ b - shift ↔ a ≤ b := sub_le_sub_iff_right shift

theorem shifted_active_upper_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c : ℕ → ℝ} (scale : ℕ → ℕ → ℝ)
    (r p : ι → ℝ) (next q : ℝ) (j : ℕ)
    (hs : ∀ᶠ n in atTop, 0 < scale j n) (hc : c =o[atTop] scale j)
    (hgap : ∀ i, q < p i → x i =o[atTop] scale j)
    (hactive : ∀ᶠ n in atTop,
      (∑ i, r i * x i n) + c n - (∑ k ∈ Finset.range j, scale k n) ≤
      (∑ i, next * x i n) - (∑ k ∈ Finset.range (j + 1), scale k n)) :
    ∃ i, p i ≤ q := by
  apply active_upper_cut (fun i => r i - next) p q hs hc hgap
  filter_upwards [hactive] with n hn
  simp only [Finset.sum_range_succ, sub_mul, Finset.sum_sub_distrib] at hn ⊢
  linarith

theorem shifted_active_lower_cut {ι : Type uIota} [Fintype ι]
    {x : ι → ℕ → ℝ} {c : ℕ → ℝ} (scale : ℕ → ℕ → ℝ)
    (r p : ι → ℝ) (prev q : ℝ) (j : ℕ)
    (hr : ∀ i, prev < r i)
    (hs : ∀ᶠ n in atTop, 0 < scale j n) (hc : c =o[atTop] scale j)
    (hx : ∀ᶠ n in atTop, ∀ i, 0 ≤ x i n)
    (hgap : ∀ i, p i < q →
      Tendsto (fun n => x i n / scale j n) atTop atTop)
    (hactive : ∀ᶠ n in atTop,
      (∑ i, r i * x i n) + c n - (∑ k ∈ Finset.range (j + 1), scale k n) ≤
      (∑ i, prev * x i n) - (∑ k ∈ Finset.range j, scale k n)) :
    ∀ i, q ≤ p i := by
  apply active_lower_cut (fun i => r i - prev) p q (fun i => sub_pos.mpr (hr i))
    hs hc hx hgap
  filter_upwards [hactive] with n hn
  simp only [Finset.sum_range_succ, sub_mul, Finset.sum_sub_distrib] at hn ⊢
  linarith

end Problem326.AffineGluing

end

end OAI
end
end

section
section
namespace OAI


open Filter
open scoped Topology

namespace Problem326

/-- A positive gap between limiting exponents makes the ratio of powers
 tend to zero, even when the numerator's exponent varies. -/
theorem tendsto_rpow_ratio_zero {α : Type uAlpha} {l : Filter α}
    {h p : α → ℝ} {p₀ q : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ n in l, 0 < h n)
    (hp : Tendsto p l (𝓝 p₀)) (hgap : q < p₀) :
    Tendsto (fun n => h n ^ p n / h n ^ q) l (𝓝 0) := by
  have hlim := hh.rpow (hp.sub_const q) (Or.inr (sub_pos.mpr hgap))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hgap))] at hlim
  apply hlim.congr'
  filter_upwards [hhpos] with n hn
  exact Real.rpow_sub hn (p n) q

/-- A negative limiting exponent gap makes the same ratio diverge. -/
theorem tendsto_rpow_ratio_atTop {α : Type uAlpha} {l : Filter α}
    {h p : α → ℝ} {p₀ q : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ n in l, 0 < h n)
    (hp : Tendsto p l (𝓝 p₀)) (hgap : p₀ < q) :
    Tendsto (fun n => h n ^ p n / h n ^ q) l atTop := by
  have hlim := hh.rpow (tendsto_const_nhds.sub hp)
    (Or.inr (sub_pos.mpr hgap))
  simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hgap))] at hlim
  have hpos : ∀ᶠ n in l, 0 < h n ^ (q - p n) := by
    filter_upwards [hhpos] with n hn
    exact Real.rpow_pos_of_pos hn _
  have hinv := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, hpos⟩)
  apply hinv.congr'
  filter_upwards [hhpos] with n hn
  simp only [Function.comp_apply, Real.rpow_sub hn, inv_div]

/-- Little-o form of the varying-exponent comparison. -/
theorem varying_rpow_isLittleO {α : Type uAlpha} {l : Filter α}
    {h p : α → ℝ} {p₀ q : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ n in l, 0 < h n)
    (hp : Tendsto p l (𝓝 p₀)) (hgap : q < p₀) :
    (fun n => h n ^ p n) =o[l] (fun n => h n ^ q) := by
  apply Asymptotics.isLittleO_of_tendsto' _
    (tendsto_rpow_ratio_zero hh hhpos hp hgap)
  filter_upwards [hhpos] with n hn
  intro hz
  exact False.elim ((ne_of_gt (Real.rpow_pos_of_pos hn q)) hz)

/-- Fixed distinct powers are asymptotically separated at zero from the right. -/
theorem rpow_isLittleO_at_zero {p q : ℝ} (hpq : q < p) :
    (fun h : ℝ => h ^ p) =o[𝓝[>] 0] (fun h => h ^ q) :=
  varying_rpow_isLittleO nhdsWithin_le_nhds
    self_mem_nhdsWithin tendsto_const_nhds hpq

/-- The exponents corresponding to any fixed initial state tend to zero. -/
theorem tendsto_log_ratio_zero (x : ℝ) :
    Tendsto (fun h : ℝ => Real.log x / Real.log h) (𝓝[>] 0) (𝓝 0) :=
  Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log x)

/-- One small parameter simultaneously controls every fixed initial exponent
 and a prescribed rate-separation inequality. -/
theorem exists_small_parameter_of_constants {ι : Type uIota} [Finite ι] (x : ι → ℝ)
    {H h₀ B : ℝ} (hH : 0 < H) (hh₀ : 0 < h₀) (hB : 0 < B) (A : ℝ) :
    ∃ h : ℝ, 0 < h ∧ h < h₀ ∧ h < 1 ∧
      (∀ i, |Real.log (x i) / Real.log h| < H) ∧ h ^ H * A < B := by
  have hbase : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlogs : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ i, |Real.log (x i) / Real.log h| < H := by
    apply eventually_all.mpr
    intro i
    have hi := (tendsto_log_ratio_zero (x i)).abs
    simp only [abs_zero] at hi
    exact hi.eventually_lt_const hH
  have hpowers : ∀ᶠ h : ℝ in 𝓝[>] 0, h ^ H * A < B := by
    have hl := (hbase.rpow_const_nhds_zero hH).mul_const A
    simp only [zero_mul] at hl
    exact hl.eventually_lt_const hB
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < h₀ :=
    hbase.eventually_lt_const hh₀
  have hone : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    hbase.eventually_lt_const zero_lt_one
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  exact (hpositive.and (hsmall.and (hone.and (hlogs.and hpowers)))).exists

end Problem326

end OAI
end
end

section
section
namespace OAI


/-! Elementary interval-gluing facts for the affine-label construction. -/
namespace Problem326.IntervalGluing

/-- Removing nonmaximal members of a finite family preserves its union. -/
theorem exists_maximal_subfamily {α : Type uAlpha} {β : Type uBeta} (S : Finset α) (U : α → Set β) :
    ∃ T : Finset α, T ⊆ S ∧
      (∀ x ∈ S, ∃ y ∈ T, U x ⊆ U y) ∧
      (∀ x ∈ T, ∀ y ∈ T, U x ⊆ U y → U y ⊆ U x) := by
  classical
  let T := S.filter (fun x => MaximalFor (· ∈ S) U x)
  refine ⟨T, Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    obtain ⟨V, hxV, hV⟩ := (S.image U).exists_le_maximal (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV.1
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, hy, ?_⟩, hxV⟩
    intro z hz hyz
    exact hV.2 (Finset.mem_image.mpr ⟨z, hz, rfl⟩) hyz
  · intro x hx y hy hxy
    have hmax := (Finset.mem_filter.mp hx).2
    exact hmax.2 (Finset.mem_filter.mp hy).1 hxy

/-- For centered intervals, noncontainment forces both endpoints to follow the
order of the centers. -/
theorem endpoints_order_of_noncontainment {t u r s : ℝ}
    (htu : t < u)
    (hntu : ¬ Set.Ioo (t-r) (t+r) ⊆ Set.Ioo (u-s) (u+s))
    (hnut : ¬ Set.Ioo (u-s) (u+s) ⊆ Set.Ioo (t-r) (t+r)) :
    t-r < u-s ∧ t+r < u+s := by
  constructor
  · by_contra h
    apply hntu
    apply Set.Ioo_subset_Ioo
    · exact le_of_not_gt h
    · linarith
  · by_contra h
    apply hnut
    apply Set.Ioo_subset_Ioo
    · linarith
    · exact le_of_not_gt h

/-- Two nonempty centered intervals with mutual inclusion have equal centers. -/
theorem center_eq_of_mutual_subset {t u r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h₁ : Set.Ioo (t-r) (t+r) ⊆ Set.Ioo (u-s) (u+s))
    (h₂ : Set.Ioo (u-s) (u+s) ⊆ Set.Ioo (t-r) (t+r)) : t = u := by
  have h₁' := (Set.Ioo_subset_Ioo_iff (show t-r < t+r by linarith)).mp h₁
  have h₂' := (Set.Ioo_subset_Ioo_iff (show u-s < u+s by linarith)).mp h₂
  linarith

/-- An arbitrary positive radius function on a compact interval has a finite
centered subcover whose centers and both endpoint lists are strictly ordered.
No continuity of the radius function is required. -/
theorem exists_ordered_interval_cover {a b : ℝ} (hab : a ≤ b)
    (r : ℝ → ℝ) (hr : ∀ t ∈ Set.Icc a b, 0 < r t) :
    ∃ n : ℕ, ∃ t : Fin (n+1) → ℝ,
      StrictMono t ∧ (∀ i, t i ∈ Set.Icc a b) ∧
      StrictMono (fun i => t i - r (t i)) ∧
      StrictMono (fun i => t i + r (t i)) ∧
      (∀ x ∈ Set.Icc a b, ∃ i, x ∈ Set.Ioo (t i-r (t i)) (t i+r (t i))) := by
  classical
  let U : ℝ → Set ℝ := fun t => Set.Ioo (t-r t) (t+r t)
  have hcov : Set.Icc a b ⊆ ⋃ t ∈ Set.Icc a b, U t := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    have := hr x hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨S', hS', hSf, hcovS⟩ :=
    isCompact_Icc.elim_finite_subcover_image (fun _ _ => isOpen_Ioo) hcov
  let S := hSf.toFinset
  obtain ⟨T, hTS, hdom, hmax⟩ := exists_maximal_subfamily S U
  have hTmem : ∀ t ∈ T, t ∈ Set.Icc a b := by
    intro t ht
    exact hS' (by simpa [S] using hTS ht)
  have hTcov : ∀ x ∈ Set.Icc a b, ∃ t ∈ T, x ∈ U t := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp (hcovS hx)
    obtain ⟨t, ht, hut⟩ := hdom u (by simpa [S] using hu)
    exact ⟨t, ht, hut hxu⟩
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, _⟩ := hTcov a ⟨le_rfl, hab⟩
    exact ⟨t, ht⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hTne.card_pos)
  let t : Fin (n+1) ↪o ℝ := T.orderEmbOfFin hn
  have htmem : ∀ i, t i ∈ T := T.orderEmbOfFin_mem hn
  have htnot : ∀ i j, i < j → ¬ U (t i) ⊆ U (t j) := by
    intro i j hij hsub
    have heq := center_eq_of_mutual_subset
      (hr _ (hTmem _ (htmem i))) (hr _ (hTmem _ (htmem j)))
      hsub (hmax _ (htmem i) _ (htmem j) hsub)
    exact (ne_of_lt (t.strictMono hij)) heq
  have htends : ∀ i j, i < j →
      t i-r (t i) < t j-r (t j) ∧ t i+r (t i) < t j+r (t j) := by
    intro i j hij
    apply endpoints_order_of_noncontainment (t.strictMono hij) (htnot i j hij)
    intro hsub
    exact htnot i j hij (hmax _ (htmem j) _ (htmem i) hsub)
  refine ⟨n, t, t.strictMono, (fun i => hTmem _ (htmem i)),
    (fun _ _ hij => (htends _ _ hij).1),
    (fun _ _ hij => (htends _ _ hij).2), ?_⟩
  intro x hx
  obtain ⟨u, hu, hxu⟩ := hTcov x hx
  have hurange : u ∈ Set.range t := by
    rw [show Set.range t = (T : Set ℝ) from T.range_orderEmbOfFin hn]
    exact hu
  obtain ⟨i, rfl⟩ := hurange
  exact ⟨i, hxu⟩

/-- Overlapping intervals with ordered centers admit a transition cut inside both
intervals and strictly between their centers. -/
theorem exists_overlap_cut {t u L R L' R' : ℝ}
    (htu : t < u) (hLt : L < t) (htR : t < R)
    (hLu : L' < u) (huR : u < R') (hoverlap : L' < R) :
    ∃ q : ℝ, t < q ∧ q < u ∧ q ∈ Set.Ioo L R ∧ q ∈ Set.Ioo L' R' := by
  have hgap : max t L' < min u R := by
    exact max_lt (lt_min htu htR) (lt_min hLu hoverlap)
  obtain ⟨q, hqlo, hqhi⟩ := exists_between hgap
  have htq : t < q := lt_of_le_of_lt (le_max_left _ _) hqlo
  have hLq : L' < q := lt_of_le_of_lt (le_max_right _ _) hqlo
  have hqu : q < u := lt_of_lt_of_le hqhi (min_le_left _ _)
  have hqR : q < R := lt_of_lt_of_le hqhi (min_le_right _ _)
  exact ⟨q, htq, hqu, ⟨hLt.trans htq, hqR⟩, ⟨hLq, hqu.trans huR⟩⟩

/-- In an ordered interval cover, neighboring intervals overlap. Ordering both
endpoints is the property obtained by deleting contained intervals. -/
theorem consecutive_overlap {n : ℕ} {a b : ℝ}
    (t L R : Fin (n + 1) → ℝ)
    (hL : StrictMono L) (hR : StrictMono R)
    (hcenter : ∀ j, L j < t j ∧ t j < R j)
    (hcenter_mem : ∀ j, t j ∈ Set.Icc a b)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ j, x ∈ Set.Ioo (L j) (R j))
    (i : Fin n) : L i.succ < R i.castSucc := by
  by_contra h
  have hgap : R i.castSucc ≤ L i.succ := le_of_not_gt h
  have hx : R i.castSucc ∈ Set.Icc a b := by
    constructor
    · exact (hcenter_mem i.castSucc).1.trans (hcenter i.castSucc).2.le
    · exact hgap.trans ((hcenter i.succ).1.le.trans (hcenter_mem i.succ).2)
  obtain ⟨j, hjL, hjR⟩ := hcover (R i.castSucc) hx
  by_cases hji : j ≤ i.castSucc
  · exact (not_lt_of_ge (hR.monotone hji)) hjR
  · have hij : i.succ ≤ j := by
      change i.val + 1 ≤ j.val
      have : i.castSucc < j := lt_of_not_ge hji
      change i.val < j.val at this
      omega
    exact (not_lt_of_ge (hgap.trans (hL.monotone hij))) hjL

/-- A simultaneous choice of all transition cuts in an ordered interval cover. -/
theorem exists_consecutive_cuts {n : ℕ} {a b : ℝ}
    (t L R : Fin (n + 1) → ℝ)
    (ht : StrictMono t) (hL : StrictMono L) (hR : StrictMono R)
    (hcenter : ∀ j, L j < t j ∧ t j < R j)
    (hcenter_mem : ∀ j, t j ∈ Set.Icc a b)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ j, x ∈ Set.Ioo (L j) (R j)) :
    ∃ q : Fin n → ℝ, ∀ i,
      t i.castSucc < q i ∧ q i < t i.succ ∧
      q i ∈ Set.Ioo (L i.castSucc) (R i.castSucc) ∧
      q i ∈ Set.Ioo (L i.succ) (R i.succ) := by
  have hex : ∀ i : Fin n, ∃ q : ℝ,
      t i.castSucc < q ∧ q < t i.succ ∧
      q ∈ Set.Ioo (L i.castSucc) (R i.castSucc) ∧
      q ∈ Set.Ioo (L i.succ) (R i.succ) := by
    intro i
    apply exists_overlap_cut (ht (by simp))
      (hcenter i.castSucc).1 (hcenter i.castSucc).2
      (hcenter i.succ).1 (hcenter i.succ).2
    exact consecutive_overlap t L R hL hR hcenter hcenter_mem hcover i
  exact Classical.axiomOfChoice hex

/-- In an ordered centered cover, the first and last intervals contain the
corresponding endpoints of the covered compact interval. -/
theorem endpoint_membership {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (t L R : Fin (n+1) → ℝ) (hL : StrictMono L) (hR : StrictMono R)
    (hcenter : ∀ j, L j < t j ∧ t j < R j)
    (hcenter_mem : ∀ j, t j ∈ Set.Icc a b)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ j, x ∈ Set.Ioo (L j) (R j)) :
    a ∈ Set.Ioo (L 0) (R 0) ∧
    b ∈ Set.Ioo (L (Fin.last n)) (R (Fin.last n)) := by
  obtain ⟨i, hi⟩ := hcover a ⟨le_rfl, hab⟩
  obtain ⟨j, hj⟩ := hcover b ⟨hab, le_rfl⟩
  constructor
  · exact ⟨(hL.monotone (Fin.zero_le i)).trans_lt hi.1,
      (hcenter_mem 0).1.trans_lt (hcenter 0).2⟩
  · exact ⟨(hcenter (Fin.last n)).1.trans_le (hcenter_mem (Fin.last n)).2,
      hj.2.trans_le (hR.monotone (Fin.le_last j))⟩

/-- Finite interval gluing data for an arbitrary positive radius function.
The chosen transition cuts lie in both adjacent intervals and strictly between
adjacent centers. Together with endpoint membership this covers every closed
piece between successive cuts by its designated interval. -/
theorem exists_interval_gluing {a b : ℝ} (hab : a ≤ b)
    (r : ℝ → ℝ) (hr : ∀ t ∈ Set.Icc a b, 0 < r t) :
    ∃ n : ℕ, ∃ t : Fin (n+1) → ℝ, ∃ q : Fin n → ℝ,
      StrictMono t ∧ (∀ i, t i ∈ Set.Icc a b) ∧
      (a ∈ Set.Ioo (t 0-r (t 0)) (t 0+r (t 0))) ∧
      (b ∈ Set.Ioo (t (Fin.last n)-r (t (Fin.last n)))
        (t (Fin.last n)+r (t (Fin.last n)))) ∧
      (∀ i, t i.castSucc < q i ∧ q i < t i.succ ∧
        q i ∈ Set.Ioo (t i.castSucc-r (t i.castSucc))
          (t i.castSucc+r (t i.castSucc)) ∧
        q i ∈ Set.Ioo (t i.succ-r (t i.succ)) (t i.succ+r (t i.succ))) := by
  obtain ⟨n, t, ht, htm, hL, hR, hcover⟩ := exists_ordered_interval_cover hab r hr
  have hcenter : ∀ i, t i-r (t i) < t i ∧ t i < t i+r (t i) := by
    intro i
    have := hr (t i) (htm i)
    constructor <;> linarith
  obtain ⟨q, hq⟩ := exists_consecutive_cuts t
    (fun i => t i-r (t i)) (fun i => t i+r (t i)) ht hL hR hcenter htm hcover
  have he := endpoint_membership hab t
    (fun i => t i-r (t i)) (fun i => t i+r (t i)) hL hR hcenter htm hcover
  exact ⟨n, t, q, ht, htm, he.1, he.2, hq⟩

end Problem326.IntervalGluing

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.Affine

/-- The cumulative shift assigned to a local family at level `j`. -/
def shiftedLabel {d : ℕ} (q : ℕ → ℝ) (j : ℕ) (L : Label d) : Label d :=
  ⟨L.slope, fun h => L.offset h - ∑ k ∈ Finset.range j, h ^ q k⟩

/-- Union of the shifted local families, with levels numbered `0, ..., N`. -/
def gluedFamily {d : ℕ} (N : ℕ) (q : ℕ → ℝ)
    (Λ : ℕ → Finset (Label d)) : Finset (Label d) := by
  classical
  exact (Finset.range (N + 1)).biUnion fun j => (Λ j).image (shiftedLabel q j)

@[simp] lemma shiftedLabel_slope {d : ℕ} (q : ℕ → ℝ) (j : ℕ) (L : Label d) :
    (shiftedLabel q j L).slope = L.slope := rfl

@[simp] lemma shiftedLabel_value {d : ℕ} (q : ℕ → ℝ) (j : ℕ)
    (L : Label d) (h : ℝ) (x : Fin d → ℝ) :
    (shiftedLabel q j L).value h x = L.value h x - ∑ k ∈ Finset.range j, h ^ q k := by
  unfold Label.value shiftedLabel
  dsimp
  ring

lemma shiftedLabel_mem_gluedFamily {d : ℕ} {N j : ℕ} {q : ℕ → ℝ}
    {Λ : ℕ → Finset (Label d)} {L : Label d} (hj : j ≤ N) (hL : L ∈ Λ j) :
    shiftedLabel q j L ∈ gluedFamily N q Λ := by
  classical
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩

lemma mem_gluedFamily_iff {d : ℕ} {N : ℕ} {q : ℕ → ℝ}
    {Λ : ℕ → Finset (Label d)} {L : Label d} :
    L ∈ gluedFamily N q Λ ↔
      ∃ j ≤ N, ∃ J ∈ Λ j, shiftedLabel q j J = L := by
  classical
  simp only [gluedFamily, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, J, hJ, heq⟩
    exact ⟨j, by omega, J, hJ, heq⟩
  · rintro ⟨j, hj, J, hJ, heq⟩
    exact ⟨j, by omega, J, hJ, heq⟩

lemma active_gluedFamily_restrict {d : ℕ} {N j : ℕ} {q : ℕ → ℝ}
    {Λ : ℕ → Finset (Label d)} {L : Label d} {h : ℝ} {x : Fin d → ℝ}
    (hj : j ≤ N) (hL : L ∈ Λ j)
    (ha : Active (gluedFamily N q Λ) (shiftedLabel q j L) h x) :
    Active (Λ j) L h x := by
  refine ⟨hL, fun J hJ => ?_⟩
  have hc := ha.2 (shiftedLabel q j J) (shiftedLabel_mem_gluedFamily hj hJ)
  simpa only [shiftedLabel_value, sub_le_sub_iff_right] using hc

lemma gluedFamily_nonempty {d : ℕ} (N : ℕ) (q : ℕ → ℝ)
    (Λ : ℕ → Finset (Label d)) (hΛ : (Λ 0).Nonempty) :
    (gluedFamily N q Λ).Nonempty := by
  obtain ⟨L, hL⟩ := hΛ
  exact ⟨shiftedLabel q 0 L, shiftedLabel_mem_gluedFamily (Nat.zero_le N) hL⟩

/-- The full sequential approximation conclusion, with unrestricted approximating
exponent vectors, as required by the dimensional induction. -/
def Approximates {d : ℕ} (Λ : Finset (Label d)) (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- Compactness of the coordinate index supplies a least exponent. -/
lemma exists_hasMinimum {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ) :
    ∃ t, HasMinimum p t := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.univ.exists_min_image p Finset.univ_nonempty
  exact ⟨p i, (fun j => hmin j (Finset.mem_univ _)), i, rfl⟩

/-- Assemble local fixed-minimum families into a global approximation family.
The two decay hypotheses are precisely those ensured by choosing each cut inside
both adjacent validity intervals. The local guarantees include the cut endpoints. -/
theorem gluedFamily_approximates {d N : ℕ} (hd : 0 < d)
    (t q : ℕ → ℝ) (Λ : ℕ → Finset (Label d)) (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ)
    (hbaseline : ∀ j ≤ N, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (hslope : ∀ j ≤ N, ∀ L ∈ Λ j, ∀ i, t j ≤ L.slope i)
    (hcenters : ∀ j < N, t j < t (j + 1))
    (hupperdecay : ∀ j < N, ∀ L ∈ Λ j,
      L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ q j))
    (hlowerdecay : ∀ j < N, ∀ L ∈ Λ (j + 1),
      L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ q j))
    (hlocal : ∀ j ≤ N, ∀ μ ∈ Set.Icc a b,
      (j = 0 ∨ q (j - 1) ≤ μ) → (j = N ∨ μ ≤ q j) →
      ApproximatesAtMinimum (Λ j) a b μ E) :
    Approximates (gluedFamily N q Λ) a b E := by
  intro L hL h p p₀ hpos hh hp hp₀ hactive
  obtain ⟨j, hj, J, hJ, rfl⟩ := mem_gluedFamily_iff.mp hL
  have hh' : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hpos⟩
  have hpeval : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)) :=
    tendsto_pi_nhds.mp hp
  obtain ⟨μ, hμ⟩ := exists_hasMinimum hd p₀
  have hupper : j = N ∨ μ ≤ q j := by
    by_cases hjN : j = N
    · exact Or.inl hjN
    right
    have hjlt : j < N := by omega
    have hcomparison : ∀ᶠ n in atTop,
        (∑ i, J.slope i * h n ^ p n i) + J.offset (h n) -
          (∑ k ∈ Finset.range j, h n ^ q k) ≤
        (∑ i : Fin d, t (j + 1) * h n ^ p n i) -
          (∑ k ∈ Finset.range (j + 1), h n ^ q k) := by
      apply Eventually.of_forall
      intro n
      have hc := (hactive n).2
        (shiftedLabel q (j + 1) ⟨fun _ => t (j + 1), fun _ => 0⟩)
        (shiftedLabel_mem_gluedFamily (by omega) (hbaseline (j + 1) (by omega)))
      simp only [shiftedLabel_value] at hc
      simpa only [Label.value, powerPoint, add_zero] using hc
    obtain ⟨i, hi⟩ := AffineGluing.shifted_active_upper_cut
      (fun k n => h n ^ q k) J.slope p₀ (t (j + 1)) (q j) j
      (Eventually.of_forall fun n => Real.rpow_pos_of_pos (hpos n) _)
      ((hupperdecay j hjlt J hJ).comp_tendsto hh')
      (fun i hgap => varying_rpow_isLittleO hh (Eventually.of_forall hpos) (hpeval i) hgap)
      hcomparison
    exact (hμ.1 i).trans hi
  have hlower : j = 0 ∨ q (j - 1) ≤ μ := by
    cases j with
    | zero => exact Or.inl rfl
    | succ k =>
      right
      have hk : k < N := by omega
      have hcomparison : ∀ᶠ n in atTop,
          (∑ i, J.slope i * h n ^ p n i) + J.offset (h n) -
            (∑ l ∈ Finset.range (k + 1), h n ^ q l) ≤
          (∑ i : Fin d, t k * h n ^ p n i) -
            (∑ l ∈ Finset.range k, h n ^ q l) := by
        apply Eventually.of_forall
        intro n
        have hc := (hactive n).2
          (shiftedLabel q k ⟨fun _ => t k, fun _ => 0⟩)
          (shiftedLabel_mem_gluedFamily (by omega) (hbaseline k (by omega)))
        simp only [shiftedLabel_value] at hc
        simpa only [Label.value, powerPoint, add_zero] using hc
      have hforced := AffineGluing.shifted_active_lower_cut
        (fun l n => h n ^ q l) J.slope p₀ (t k) (q k) k
        (fun i => (hcenters k hk).trans_le (hslope (k + 1) hj J hJ i))
        (Eventually.of_forall fun n => Real.rpow_pos_of_pos (hpos n) _)
        ((hlowerdecay k hk J hJ).comp_tendsto hh')
        (Eventually.of_forall fun n i => (Real.rpow_pos_of_pos (hpos n) (p n i)).le)
        (fun i hgap => tendsto_rpow_ratio_atTop hh (Eventually.of_forall hpos) (hpeval i) hgap)
        hcomparison
      obtain ⟨i, hi⟩ := hμ.2
      simpa only [Nat.add_sub_cancel, hi] using hforced i
  have hμab : μ ∈ Set.Icc a b := by
    obtain ⟨i, hi⟩ := hμ.2
    simpa only [Set.mem_Icc, hi] using hp₀ i
  have hresult := (hlocal j hj μ hμab hlower hupper) J hJ h p p₀ hpos hh hp hp₀ hμ
    (fun n => active_gluedFamily_restrict hj hJ (hactive n))
  simpa only [shiftedLabel_slope] using hresult

/-- Offset decay is preserved by the cumulative shifts because every cut
exponent lies strictly above the lower endpoint. -/
lemma shiftedLabel_offset_isLittleO {d : ℕ} {a : ℝ} (q : ℕ → ℝ)
    (j : ℕ) (L : Label d)
    (hL : L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a))
    (hq : ∀ k < j, a < q k) :
    (shiftedLabel q j L).offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a) := by
  have hsum : (fun h : ℝ => ∑ k ∈ Finset.range j, h ^ q k)
      =o[𝓝[>] 0] (fun h : ℝ => h ^ a) := by
    exact IsLittleO.fun_sum (fun k hk => rpow_isLittleO_at_zero (hq k (Finset.mem_range.mp hk)))
  exact hL.sub hsum

/-- Arbitrary local radius certificates
are glued into one nonempty finite family. No regularity of `ρ`, `Γ`, or `E` is
assumed. Local guarantees on open bands suffice because all cuts lie strictly
inside both neighboring bands. -/
theorem exists_approximating_family_of_local_families {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (ρ : ℝ → ℝ) (Γ : ℝ → Finset (Label d))
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t)
    (hbaseline : ∀ t ∈ Set.Icc a b,
      (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ t)
    (hdata : ∀ t ∈ Set.Icc a b, ∀ L ∈ Γ t,
      Cube a b L.slope ∧ HasMinimum L.slope t ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ t)))
    (hlocal : ∀ t ∈ Set.Icc a b, ∀ μ : ℝ, |μ - t| < ρ t →
      ApproximatesAtMinimum (Γ t) a b μ E) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a)) ∧
      Approximates Λ a b E := by
  classical
  obtain ⟨N, c, q, hc, hcmem, hfirst, hlast, hcuts⟩ :=
    IntervalGluing.exists_interval_gluing hab ρ hρ
  let t : ℕ → ℝ := fun j => if hj : j ≤ N then c ⟨j, by omega⟩ else a
  let Q : ℕ → ℝ := fun j => if hj : j < N then q ⟨j, hj⟩ else a
  let Λ : ℕ → Finset (Label d) := fun j => Γ (t j)
  have htm : ∀ j ≤ N, t j ∈ Set.Icc a b := by
    intro j hj
    simpa [t, hj] using hcmem ⟨j, by omega⟩
  have hcut : ∀ j < N, t j < Q j ∧ Q j < t (j + 1) ∧
      Q j ∈ Set.Ioo (t j - ρ (t j)) (t j + ρ (t j)) ∧
      Q j ∈ Set.Ioo (t (j + 1) - ρ (t (j + 1))) (t (j + 1) + ρ (t (j + 1))) := by
    intro j hj
    have hjle : j ≤ N := by omega
    have hjsucc : j + 1 ≤ N := by omega
    simpa [t, Q, hj, hjle, hjsucc] using hcuts ⟨j, hj⟩
  have hfirst' : a ∈ Set.Ioo (t 0 - ρ (t 0)) (t 0 + ρ (t 0)) := by
    simpa [t] using hfirst
  have hlast' : b ∈ Set.Ioo (t N - ρ (t N)) (t N + ρ (t N)) := by
    simpa [t, Fin.last] using hlast
  have hbase : ∀ j ≤ N,
      (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j := by
    intro j hj
    exact hbaseline (t j) (htm j hj)
  have hlocal' : ∀ j ≤ N, ∀ μ ∈ Set.Icc a b,
      (j = 0 ∨ Q (j - 1) ≤ μ) → (j = N ∨ μ ≤ Q j) →
      ApproximatesAtMinimum (Λ j) a b μ E := by
    intro j hj μ hμ hlo hhi
    have hlo' : t j - ρ (t j) < μ := by
      by_cases hj0 : j = 0
      · subst j
        exact hfirst'.1.trans_le hμ.1
      · have hpred : j - 1 < N := by omega
        have hpredj : j - 1 + 1 = j := by omega
        have hprev : t j - ρ (t j) < Q (j - 1) := by
          simpa only [hpredj] using (hcut (j - 1) hpred).2.2.2.1
        exact hprev.trans_le (hlo.resolve_left hj0)
    have hhi' : μ < t j + ρ (t j) := by
      by_cases hjN : j = N
      · subst j
        exact hμ.2.trans_lt hlast'.2
      · have hjlt : j < N := by omega
        exact (hhi.resolve_left hjN).trans_lt (hcut j hjlt).2.2.1.2
    exact hlocal (t j) (htm j hj) μ (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have happrox : Approximates (gluedFamily N Q Λ) a b E := by
    apply gluedFamily_approximates hd t Q Λ a b E hbase
    · intro j hj L hL i
      exact (hdata (t j) (htm j hj) L hL).2.1.1 i
    · intro j hj
      exact (hcut j hj).1.trans (hcut j hj).2.1
    · intro j hj L hL
      exact ((hdata (t j) (htm j (by omega)) L hL).2.2).trans
        (rpow_isLittleO_at_zero (hcut j hj).2.2.1.2)
    · intro j hj L hL
      exact ((hdata (t (j + 1)) (htm (j + 1) (by omega)) L hL).2.2).trans
        (rpow_isLittleO_at_zero (hcut j hj).2.2.2.2)
    · exact hlocal'
  refine ⟨gluedFamily N Q Λ,
    gluedFamily_nonempty N Q Λ ⟨_, hbase 0 (Nat.zero_le N)⟩, ?_, happrox⟩
  intro L hL
  obtain ⟨j, hj, J, hJ, rfl⟩ := mem_gluedFamily_iff.mp hL
  have hJdata := hdata (t j) (htm j hj) J hJ
  refine ⟨hJdata.1, shiftedLabel_offset_isLittleO Q j J ?_ ?_⟩
  · exact hJdata.2.2.trans (rpow_isLittleO_at_zero (by
      have := hρ (t j) (htm j hj)
      have := (htm j hj).1
      linarith))
  · intro k hk
    exact (htm k (by omega)).1.trans_lt (hcut k (by omega)).1

/-- Choice-packaged form of the gluing theorem: local constructors may return
the radius and finite family existentially, and only for centers in the cube. -/
theorem exists_approximating_family_of_local_certificates {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hcert : ∀ t ∈ Set.Icc a b, ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Γ : Finset (Label d),
        (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ ∧
        (∀ L ∈ Γ, Cube a b L.slope ∧ HasMinimum L.slope t ∧
          L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ))) ∧
        (∀ μ : ℝ, |μ - t| < ρ → ApproximatesAtMinimum Γ a b μ E)) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a)) ∧
      Approximates Λ a b E := by
  classical
  have hex : ∀ t : ℝ, ∃ ρ : ℝ, ∃ Γ : Finset (Label d),
      t ∈ Set.Icc a b → 0 < ρ ∧
        (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ ∧
        (∀ L ∈ Γ, Cube a b L.slope ∧ HasMinimum L.slope t ∧
          L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ))) ∧
        (∀ μ : ℝ, |μ - t| < ρ → ApproximatesAtMinimum Γ a b μ E) := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · obtain ⟨ρ, hρ, Γ, hΓ⟩ := hcert t ht
      exact ⟨ρ, Γ, fun _ => ⟨hρ, hΓ⟩⟩
    · exact ⟨1, ∅, fun h => (ht h).elim⟩
  choose ρ Γ hΓ using hex
  exact exists_approximating_family_of_local_families hd hab E ρ Γ
    (fun t ht => (hΓ t ht).1)
    (fun t ht => (hΓ t ht).2.1)
    (fun t ht => (hΓ t ht).2.2.1)
    (fun t ht => (hΓ t ht).2.2.2)

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326.Affine

/-- The exact gluing interface used by the dimension induction. Local certificates
are first extended to nearby minimum levels with a common stronger decay radius,
then the finite interval construction glues them into one full certificate. -/
theorem glue_localCertificates {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hlocal : ∀ t : ℝ, a ≤ t → t ≤ b →
      Nonempty (LocalCertificate d a b t E)) :
    Nonempty (FullCertificate d a b E) := by
  classical
  let I := {t : ℝ // t ∈ Icc a b}
  let C (t : I) : LocalCertificate d a b t.val E :=
    Classical.choice (hlocal t.val t.property.1 t.property.2)
  choose r hr hdecay happ using fun t : I => (C t).exists_radius hd
  let ρ (t : ℝ) : ℝ := if ht : t ∈ Icc a b then r ⟨t, ht⟩ else 1
  let Γ (t : ℝ) : Finset (Label d) :=
    if ht : t ∈ Icc a b then (C ⟨t, ht⟩).labels else ∅
  have hρ (t : ℝ) (ht : t ∈ Icc a b) : 0 < ρ t := by
    simpa only [ρ, dite_eq_left ht] using hr ⟨t, ht⟩
  have hbaseline (t : ℝ) (ht : t ∈ Icc a b) :
      (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ t := by
    simpa only [Γ, dite_eq_left ht] using (C ⟨t, ht⟩).baseline
  have hdata (t : ℝ) (ht : t ∈ Icc a b) (L : Label d) (hL : L ∈ Γ t) :
      Cube a b L.slope ∧ HasMinimum L.slope t ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ t)) := by
    have hLC : L ∈ (C ⟨t, ht⟩).labels := by
      simpa only [Γ, dite_eq_left ht] using hL
    refine ⟨?_, (C ⟨t, ht⟩).minima L hLC, ?_⟩
    · intro i
      have hi := (C ⟨t, ht⟩).slopes L hLC i
      exact ⟨ht.1.trans hi.1, hi.2⟩
    · simpa only [ρ, dite_eq_left ht] using hdecay ⟨t, ht⟩ L hLC
  have hnear (t : ℝ) (ht : t ∈ Icc a b) (μ : ℝ) (hμ : |μ - t| < ρ t) :
      ApproximatesAtMinimum (Γ t) a b μ E := by
    have hμ' : |μ - t| < r ⟨t, ht⟩ := by
      simpa only [ρ, dite_eq_left ht] using hμ
    simpa only [Γ, dite_eq_left ht] using happ ⟨t, ht⟩ μ hμ'
  obtain ⟨Λ, hΛ, hdataΛ, happΛ⟩ :=
    exists_approximating_family_of_local_families hd hab E ρ Γ hρ hbaseline hdata hnear
  exact ⟨{
    labels := Λ
    nonempty := hΛ
    slopes := fun L hL => (hdataΛ L hL).1
    offsets := fun L hL => (hdataΛ L hL).2
    approximation := happΛ
  }⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326.Affine

/-- The full affine approximation certificate, obtained by dimension induction
and finite interval gluing. The tolerance need not be continuous. -/
theorem exists_fullCertificate :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate d a b E) := by
  apply fullCertificate_of_local_and_glue
  · intro d hd ih a b E hab hE t hat htb
    by_cases heq : t = b
    · subst t
      exact ⟨localCertificate_upper hd a b E (hE _ (fun _ => ⟨hab.le, le_rfl⟩))⟩
    · apply localCertificate_of_layers hd (lt_of_le_of_ne htb heq) E
        (hE _ (fun _ => ⟨hat, htb⟩))
      intro k hk hkd β htβ hβb
      obtain ⟨F, _, hF⟩ := exists_typeFamily_layerCertificate hk hkd htβ hβb E
        (fun r hr => hE r (fun i => ⟨hat.trans (hr i).1, (hr i).2⟩))
        (fun E' hE' => ih k hkd β b E' hβb hE')
      exact ⟨F, hF⟩
  · intro d hd a b E hab _ hlocal
    exact glue_localCertificates hd hab.le E hlocal

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


open Set Filter Topology

namespace Problem326

/-! Topological support for the local-to-global affine-label construction.
The parameter approaches zero through positive values; no continuity in that
parameter is assumed. -/

variable {X : Type uX} [TopologicalSpace X]

/-- Limit points of a state family as a positive real parameter tends to zero. -/
def positiveLimitSet (A : ℝ → Set X) : Set X :=
  {p | (0, p) ∈ closure {u : ℝ × X | 0 < u.1 ∧ u.2 ∈ A u.1}}

theorem isClosed_positiveLimitSet (A : ℝ → Set X) :
    IsClosed (positiveLimitSet A) := by
  exact isClosed_closure.preimage (continuous_const.prodMk continuous_id)

theorem mem_positiveLimitSet_of_tendsto {A : ℝ → Set X}
    {h : ℕ → ℝ} {q : ℕ → X} {p : X}
    (hh : Tendsto h atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 p))
    (hpos : ∀ n, 0 < h n) (hmem : ∀ n, q n ∈ A (h n)) :
    p ∈ positiveLimitSet A := by
  exact isClosed_closure.mem_of_tendsto (hh.prodMk_nhds hq)
    (Eventually.of_forall fun n => subset_closure ⟨hpos n, hmem n⟩)

theorem mem_positiveLimitSet_iff_seq [FirstCountableTopology X]
    {A : ℝ → Set X} {p : X} :
    p ∈ positiveLimitSet A ↔
      ∃ (h : ℕ → ℝ) (q : ℕ → X),
        Tendsto h atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 p) ∧
        (∀ n, 0 < h n) ∧ (∀ n, q n ∈ A (h n)) := by
  constructor
  · intro hp
    obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hp
    exact ⟨fun n => (u n).1, fun n => (u n).2,
      ht.fst_nhds, ht.snd_nhds,
      fun n => (hu n).1, fun n => (hu n).2⟩
  · rintro ⟨h, q, hh, hq, hpos, hmem⟩
    exact mem_positiveLimitSet_of_tendsto hh hq hpos hmem

theorem isCompact_positiveLimitSet_inter {A : ℝ → Set X} {K : Set X}
    (hK : IsCompact K) : IsCompact (positiveLimitSet A ∩ K) := by
  exact hK.inter_left (isClosed_positiveLimitSet A)

/-- A compact set missing a level of a continuous scalar function misses a
whole open band around that level. This also handles an empty compact set. -/
theorem exists_pos_band_disjoint {K : Set X} (hK : IsCompact K)
    {μ : X → ℝ} (hμ : ContinuousOn μ K) {t : ℝ}
    (havoid : ∀ p ∈ K, μ p ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ K, ρ ≤ |μ p - t| := by
  apply hK.exists_forall_le' ((hμ.sub continuousOn_const).abs)
  intro p hp
  exact abs_pos.mpr (sub_ne_zero.mpr (havoid p hp))

/-- The finite-family form of the neighborhood extension step. If every
limiting active label is good at one level, then this also holds in a band
around that level. The good sets are open, but the active sets may be arbitrary. -/
theorem exists_pos_band_of_limit_good {ι : Type uIota} [Finite ι]
    {K : Set X} (hK : IsCompact K) {μ : X → ℝ}
    (hμ : ContinuousOn μ K) {t : ℝ} (A : ι → ℝ → Set X)
    (G : ι → Set X) (hG : ∀ i, IsOpen (G i))
    (hgood : ∀ i p, p ∈ K → μ p = t →
      p ∈ positiveLimitSet (A i) → p ∈ G i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i p, p ∈ K → |μ p - t| < ρ →
      p ∈ positiveLimitSet (A i) → p ∈ G i := by
  let B : Set X := ⋃ i, (positiveLimitSet (A i) ∩ K) \ G i
  have hBc : IsCompact B := by
    apply isCompact_iUnion
    intro i
    exact (isCompact_positiveLimitSet_inter hK).diff (hG i)
  have hBK : B ⊆ K := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hi.1.2
  have havoid : ∀ p ∈ B, μ p ≠ t := by
    intro p hp heq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hi.2 (hgood i p hi.1.2 heq hi.1.1)
  obtain ⟨ρ, hρ, hsep⟩ := exists_pos_band_disjoint hBc (hμ.mono hBK) havoid
  refine ⟨ρ, hρ, ?_⟩
  intro i p hp hband hlim
  by_contra hbad
  have hpB : p ∈ B := mem_iUnion.mpr ⟨i, ⟨⟨hlim, hp⟩, hbad⟩⟩
  exact (not_lt_of_ge (hsep p hpB)) hband

/-- Compactness upgrades a limiting active-set inclusion into a uniform
small-parameter inclusion. No continuity of the active sets is required. -/
theorem exists_pos_uniform_of_limit_subset [FirstCountableTopology X]
    {A : ℝ → Set X} {K G : Set X} (hK : IsCompact K) (hG : IsOpen G)
    (hgood : ∀ p ∈ K, p ∈ positiveLimitSet A → p ∈ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, p ∈ A h → p ∈ G := by
  classical
  by_contra! hn
  have hex : ∀ n : ℕ, ∃ (h : ℝ) (p : X),
      0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧ p ∈ K ∧ p ∈ A h ∧ p ∉ G := by
    intro n
    obtain ⟨h, hh, hsmall, p, hpK, hpA, hpG⟩ :=
      hn (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨h, p, hh, hsmall, hpK, hpA, hpG⟩
  choose h q hpos hsmall hqK hqA hqG using hex
  have ht : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hpos n).le) (fun n => (hsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hpK, φ, hφ, hq⟩ := hK.tendsto_subseq hqK
  have hlim : p ∈ positiveLimitSet A :=
    mem_positiveLimitSet_of_tendsto (ht.comp hφ.tendsto_atTop) hq
      (fun n => hpos (φ n)) (fun n => hqA (φ n))
  have hbad : p ∈ Gᶜ := hG.isClosed_compl.mem_of_tendsto hq
    (Eventually.of_forall fun n => hqG (φ n))
  exact hbad (hgood p hpK hlim)

/-- Uniform small-parameter inclusion for any finite family of active sets. -/
theorem exists_pos_uniform_of_finite_limit_subset [FirstCountableTopology X]
    {ι : Type uIota} [Finite ι] {A : ι → ℝ → Set X} {K : Set X}
    {G : ι → Set X} (hK : IsCompact K) (hG : ∀ i, IsOpen (G i))
    (hgood : ∀ i p, p ∈ K → p ∈ positiveLimitSet (A i) → p ∈ G i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ i p, p ∈ K → p ∈ A i h → p ∈ G i := by
  classical
  have hex := fun i => exists_pos_uniform_of_limit_subset hK (hG i) (hgood i)
  choose δ hδ hδgood using hex
  have hcompact : IsCompact (Set.range δ) := (Set.finite_range δ).isCompact
  obtain ⟨δ₀, hδ₀, hmin⟩ := hcompact.exists_forall_le' continuousOn_id
    (show ∀ y ∈ Set.range δ, (0 : ℝ) < y from by
      rintro y ⟨i, rfl⟩
      exact hδ i)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro h hh hsmall i p hp hactive
  exact hδgood i h hh (lt_of_lt_of_le hsmall (hmin (δ i) ⟨i, rfl⟩))
    p hp hactive

end Problem326

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326.Affine

variable {d : ℕ}

def coordinateMinimum [NeZero d] (p : Fin d → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

theorem continuous_coordinateMinimum [NeZero d] :
    Continuous (coordinateMinimum (d := d)) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)

theorem hasMinimum_coordinateMinimum [NeZero d] (p : Fin d → ℝ) :
    HasMinimum p (coordinateMinimum p) := by
  refine ⟨fun i => Finset.inf'_le p (Finset.mem_univ i), ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
  exact ⟨i, hi.symm⟩

theorem hasMinimum_iff_coordinateMinimum_eq [NeZero d] (p : Fin d → ℝ) (t : ℝ) :
    HasMinimum p t ↔ coordinateMinimum p = t := by
  constructor
  · rintro ⟨hlower, i, hi⟩
    apply le_antisymm
    · exact (Finset.inf'_le p (Finset.mem_univ i)).trans hi.le
    · exact Finset.le_inf' Finset.univ_nonempty p (fun j _ => hlower j)
  · intro h
    rw [← h]
    exact hasMinimum_coordinateMinimum p

theorem isCompact_cube (a b : ℝ) : IsCompact {p : Fin d → ℝ | Cube a b p} := by
  have heq : {p : Fin d → ℝ | Cube a b p} = Icc (fun _ => a) (fun _ => b) := by
    ext p
    simp only [mem_ofPred_eq, Cube, mem_Icc, Pi.le_def, forall_and]
  rw [heq]
  exact isCompact_Icc

/-- Activity that approximates at a fixed minimum
continues to approximate for every limiting minimum in a positive band. -/
theorem ApproximatesAtMinimum.exists_nearby [NeZero d]
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hΛ : ApproximatesAtMinimum Λ a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ L ∈ Λ,
      ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
      |coordinateMinimum p₀ - t| < ρ →
      (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
      ‖p₀ - L.slope‖ < E L.slope := by
  classical
  let A : ℝ → (Fin d → ℝ) → ↥Λ → Prop :=
    fun h p L => Active Λ L.val h (powerPoint h p)
  obtain ⟨ρ, hρ, hnear⟩ := AffineApproximation.nearby_level_activity A
    (isCompact_cube (d := d) a b) coordinateMinimum continuous_coordinateMinimum t
    (fun L p => ‖p - L.val.slope‖)
    (fun _ => (continuous_id.sub continuous_const).norm)
    (fun L => E L.val.slope) (by
      intro L p₀ hp₀ hlim hmin
      obtain ⟨h, p, hpos, hh, hp, hactive⟩ :=
        (AffineApproximation.mem_limitActivity_iff_seq A L p₀).mp hlim
      exact hΛ L.val L.property h p p₀ hpos hh hp hp₀
        ((hasMinimum_iff_coordinateMinimum_eq p₀ t).mpr hmin) hactive)
  refine ⟨ρ, hρ, ?_⟩
  intro L hL h p p₀ hpos hh hp hp₀ hclose hactive
  apply hnear ⟨L, hL⟩ p₀ hp₀ _ hclose
  exact (AffineApproximation.mem_limitActivity_iff_seq A ⟨L, hL⟩ p₀).mpr
    ⟨h, p, hpos, hh, hp, hactive⟩

/-- The full sequential conclusion of the affine approximation lemma. -/
def ApproximatesOnCube (Λ : Finset (Label d))
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- Uniform-activity corollary for the exact affine-label interface. -/
theorem ApproximatesOnCube.uniform_activity
    {Λ : Finset (Label d)} {a b : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hΛ : ApproximatesOnCube Λ a b E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p, Cube a b p → ∀ L ∈ Λ,
      Active Λ L h (powerPoint h p) → ‖p - L.slope‖ < E L.slope := by
  classical
  let A : ℝ → (Fin d → ℝ) → ↥Λ → Prop :=
    fun h p L => Active Λ L.val h (powerPoint h p)
  obtain ⟨δ, hδ, hbound⟩ := AffineApproximation.uniform_activity_of_sequence A
    (isCompact_cube (d := d) a b)
    (fun L p => ‖p - L.val.slope‖)
    (fun _ => (continuous_id.sub continuous_const).norm)
    (fun L => E L.val.slope) (by
      intro L p₀ hp₀ h p hpos hh hp hactive
      exact hΛ L.val L.property h p p₀ hpos hh hp hp₀ hactive)
  exact ⟨δ, hδ, fun h hh hsmall p hp L hL hactive =>
    hbound h hh hsmall p hp ⟨L, hL⟩ hactive⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326

def IsForwardSolutionOn {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x0 : Fin d → ℝ) (T : ℝ)
    (x : ℝ → (Fin d → ℝ)) : Prop :=
  x 0 = x0 ∧
    ContinuousOn x (Set.Icc (0 : ℝ) T) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt x (massAction N κ (x t)) t

def dot {d : ℕ} (a x : Fin d → ℝ) : ℝ :=
  Finset.univ.sum (fun i => a i * x i)

def IsFinitePolyhedron {d : ℕ} (K : Set (Fin d → ℝ)) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → (Fin d → ℝ), ∃ b : Fin n → ℝ,
    K = {x | ∀ j, b j ≤ dot (a j) x}

def IsForwardInvariant {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (K : Set (Fin d → ℝ)) : Prop :=
  ∀ z, z ∈ K →
    (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ z x) ∧
    ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)), 0 ≤ T →
      IsForwardSolutionOn N κ z T x →
      (∀ t ∈ Set.Icc (0 : ℝ) T, x t ∈ K) ∧
      ∃ xg : ℝ → (Fin d → ℝ),
        IsGlobalForwardSolution N κ z xg ∧
        Set.EqOn xg x (Set.Icc (0 : ℝ) T)

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326.Geometry

/-- Boundary exclusion traps any preconnected set that meets the interior.
This is the purely topological step in the plateau-polytope construction. -/
theorem subset_interior_of_disjoint_frontier
    {X : Type uX} [TopologicalSpace X] {K B : Set X}
    (hK : IsPreconnected K) (hmeet : (K ∩ interior B).Nonempty)
    (hboundary : Disjoint K (frontier B)) : K ⊆ interior B := by
  apply hK.subset_of_closure_inter_subset isOpen_interior hmeet
  intro x hx
  by_contra hnot
  apply Set.disjoint_left.mp hboundary hx.2
  exact ⟨closure_mono interior_subset hx.1, hnot⟩

/-- A closed preconnected plateau that meets the interior of a compact box
and misses its boundary is compact. No boundedness assumption on the
ambient compatibility class is needed. -/
theorem isCompact_of_disjoint_frontier
    {X : Type uX} [TopologicalSpace X] {K B : Set X}
    (hKclosed : IsClosed K) (hKconn : IsPreconnected K)
    (hBcompact : IsCompact B) (hmeet : (K ∩ interior B).Nonempty)
    (hboundary : Disjoint K (frontier B)) : IsCompact K := by
  apply hBcompact.of_isClosed_subset hKclosed
  exact (subset_interior_of_disjoint_frontier hKconn hmeet hboundary).trans interior_subset

end Problem326.Geometry

namespace Problem326.Geometry

/-- A continuous curve cannot leave an interior if each segment in the
closed ambient set is forbidden from ending on its boundary. -/
theorem mapsTo_interior_of_no_first_boundary
    {X : Type uX} [TopologicalSpace X] {B : Set X} {T : ℝ}
    {x : ℝ → X} (hT : 0 ≤ T) (hB : IsClosed B)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx0 : x 0 ∈ interior B)
    (hblock : ∀ τ ∈ Set.Icc 0 T,
      Set.MapsTo x (Set.Icc 0 τ) B → x τ ∉ frontier B) :
    Set.MapsTo x (Set.Icc 0 T) (interior B) := by
  have hconn : IsPreconnected (x '' Set.Icc 0 T) :=
    isPreconnected_Icc.image x hx
  have hmeet : ((x '' Set.Icc 0 T) ∩ interior B).Nonempty :=
    ⟨x 0, ⟨0, ⟨le_rfl, hT⟩, rfl⟩, hx0⟩
  suffices hd : Disjoint (x '' Set.Icc 0 T) (frontier B) by
    intro t ht
    exact subset_interior_of_disjoint_frontier hconn hmeet hd ⟨t, ht, rfl⟩
  by_contra hnot
  have hnonempty : (Set.Icc 0 T ∩ x ⁻¹' frontier B).Nonempty := by
    obtain ⟨z, hz, hb⟩ := Set.not_disjoint_iff.mp hnot
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, hb⟩
  have hc : IsCompact (Set.Icc 0 T ∩ x ⁻¹' frontier B) := by
    exact isCompact_Icc.of_isClosed_subset
      (hx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier)
      Set.inter_subset_left
  obtain ⟨τ, hτ, hmin⟩ := hc.exists_isMinOn hnonempty continuousOn_id
  apply hblock τ hτ.1 ?_ hτ.2
  intro s hs
  rcases hs.2.eq_or_lt with hst | hst
  · simpa [hst] using hB.frontier_subset hτ.2
  · have hsub : Set.Icc 0 s ⊆ Set.Icc 0 T :=
      Set.Icc_subset_Icc le_rfl (le_trans hs.2 hτ.1.2)
    have hd : Disjoint (x '' Set.Icc 0 s) (frontier B) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨t, ht, rfl⟩ hb
      have hτt : τ ≤ t := hmin ⟨hsub ht, hb⟩
      exact (not_le_of_gt hst) (le_trans hτt ht.2)
    have hm : ((x '' Set.Icc 0 s) ∩ interior B).Nonempty :=
      ⟨x 0, ⟨0, ⟨le_rfl, hs.1⟩, rfl⟩, hx0⟩
    exact interior_subset
      (subset_interior_of_disjoint_frontier
        (isPreconnected_Icc.image x (hx.mono hsub)) hm hd
        ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩)

end Problem326.Geometry

namespace Problem326.Geometry

/-- Monotonicity inside a box, together with a global ceiling and exclusion
of boundary maximizers, confines a whole continuous segment to its plateau. -/
theorem mapsTo_plateau_of_monotone_on_box
    {X : Type uX} [TopologicalSpace X] {B : Set X} {T M : ℝ}
    {x : ℝ → X} {F : X → ℝ} (hT : 0 ≤ T) (hB : IsClosed B)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx0 : x 0 ∈ interior B)
    (hFM : ∀ z, F z ≤ M) (hF0 : F (x 0) = M)
    (hboundary : ∀ z ∈ frontier B, F z ≠ M)
    (hmono : ∀ τ ∈ Set.Icc 0 T, Set.MapsTo x (Set.Icc 0 τ) B →
      MonotoneOn (F ∘ x) (Set.Icc 0 τ)) :
    Set.MapsTo x (Set.Icc 0 T) {z | z ∈ interior B ∧ F z = M} := by
  have hinside : Set.MapsTo x (Set.Icc 0 T) (interior B) := by
    apply mapsTo_interior_of_no_first_boundary hT hB hx hx0
    intro τ hτ hseg hb
    apply hboundary (x τ) hb
    apply le_antisymm (hFM _)
    calc
      M = F (x 0) := hF0.symm
      _ ≤ F (x τ) := hmono τ hτ hseg ⟨le_rfl, hτ.1⟩ ⟨hτ.1, le_rfl⟩ hτ.1
  have hseg : Set.MapsTo x (Set.Icc 0 T) B :=
    fun t ht => interior_subset (hinside ht)
  intro t ht
  refine ⟨hinside ht, le_antisymm (hFM _) ?_⟩
  calc
    M = F (x 0) := hF0.symm
    _ ≤ F (x t) := hmono T ⟨hT, le_rfl⟩ hseg ⟨le_rfl, hT⟩ ht ht.1

end Problem326.Geometry

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
namespace Problem326
variable {d : ℕ}

lemma continuous_dot (a : Fin d → ℝ) : Continuous (dot a) := by
  unfold dot
  fun_prop

lemma dot_add_right (a x y : Fin d → ℝ) : dot a (x + y) = dot a x + dot a y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul_right (a x : Fin d → ℝ) (c : ℝ) : dot a (c • x) = c * dot a x := by
  simp [dot, Finset.mul_sum, mul_left_comm]

lemma dot_isLinearMap (a : Fin d → ℝ) : IsLinearMap ℝ (dot a) := by
  constructor
  · exact dot_add_right a
  · intro c x
    exact dot_smul_right a x c

lemma IsFinitePolyhedron.isClosed {K : Set (Fin d → ℝ)}
    (hK : IsFinitePolyhedron K) : IsClosed K := by
  rcases hK with ⟨n, a, b, rfl⟩
  have heq : {x | ∀ j, b j ≤ dot (a j) x} =
      ⋂ j, {x | b j ≤ dot (a j) x} := by ext x; simp
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_dot (a j))

lemma IsFinitePolyhedron.convex {K : Set (Fin d → ℝ)}
    (hK : IsFinitePolyhedron K) : Convex ℝ K := by
  rcases hK with ⟨n, a, b, rfl⟩
  have heq : {x | ∀ j, b j ≤ dot (a j) x} =
      ⋂ j, {x | b j ≤ dot (a j) x} := by ext x; simp
  rw [heq]
  exact convex_iInter fun j => convex_halfSpace_ge (dot_isLinearMap (a j)) (b j)

lemma finiteAffine_superlevel_isFinitePolyhedron {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ) :
    IsFinitePolyhedron {x | ∀ j, M ≤ dot (a j) x + c j} := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, (fun j => a (e.symm j)),
    (fun j => M - c (e.symm j)), ?_⟩
  ext x
  constructor
  · intro h j
    have := h (e.symm j)
    linarith
  · intro h j
    have hj := h (e j)
    simp only [Equiv.symm_apply_apply] at hj
    linarith

lemma finiteAffine_superlevel_isClosed {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ) :
    IsClosed {x | ∀ j, M ≤ dot (a j) x + c j} :=
  (finiteAffine_superlevel_isFinitePolyhedron a c M).isClosed

lemma finiteAffine_superlevel_convex {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ) :
    Convex ℝ {x | ∀ j, M ≤ dot (a j) x + c j} :=
  (finiteAffine_superlevel_isFinitePolyhedron a c M).convex

/-- A capped finite lower envelope has a polyhedral maximum set.
This interface is independent of the choice of finite-minimum notation. -/
lemma finiteAffine_plateau_eq {ι : Type uIota}
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (F : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hlower : ∀ x j, F x ≤ dot (a j) x + c j)
    (hattained : ∀ x, ∃ j, F x = dot (a j) x + c j)
    (hceiling : ∀ x, F x ≤ M) :
    {x | F x = M} = {x | ∀ j, M ≤ dot (a j) x + c j} := by
  ext x
  constructor
  · intro hx j
    change F x = M at hx
    simpa only [hx] using hlower x j
  · intro hx
    obtain ⟨j, hj⟩ := hattained x
    exact le_antisymm (hceiling x) (by simpa only [hj] using hx j)

lemma finiteAffine_plateau_isFinitePolyhedron {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (F : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hlower : ∀ x j, F x ≤ dot (a j) x + c j)
    (hattained : ∀ x, ∃ j, F x = dot (a j) x + c j)
    (hceiling : ∀ x, F x ≤ M) :
    IsFinitePolyhedron {x | F x = M} := by
  rw [finiteAffine_plateau_eq a c F M hlower hattained hceiling]
  exact finiteAffine_superlevel_isFinitePolyhedron a c M

/-- Finite affine barriers which exclude the boundary of a compact set
produce a compact convex polyhedron in its interior. -/
lemma compact_polyhedron_of_affine_barriers {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (M : ℝ)
    (B : Set (Fin d → ℝ)) (x0 : Fin d → ℝ)
    (hB : IsCompact B) (hx0B : x0 ∈ interior B)
    (hx0 : ∀ j, M ≤ dot (a j) x0 + c j)
    (hboundary : ∀ x ∈ frontier B, ∃ j, dot (a j) x + c j < M) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ Convex ℝ K ∧
      IsFinitePolyhedron K ∧ x0 ∈ K ∧ K ⊆ interior B ∧
      ∀ x, x ∈ K ↔ ∀ j, M ≤ dot (a j) x + c j := by
  let K : Set (Fin d → ℝ) := {x | ∀ j, M ≤ dot (a j) x + c j}
  have hpoly : IsFinitePolyhedron K := finiteAffine_superlevel_isFinitePolyhedron a c M
  have hconv : Convex ℝ K := hpoly.convex
  have hdisjoint : Disjoint K (frontier B) := by
    rw [Set.disjoint_left]
    intro x hx hxB
    obtain ⟨j, hj⟩ := hboundary x hxB
    exact (not_lt_of_ge (hx j)) hj
  have hmeet : (K ∩ interior B).Nonempty := ⟨x0, hx0, hx0B⟩
  have hsub : K ⊆ interior B :=
    Geometry.subset_interior_of_disjoint_frontier hconv.isPreconnected hmeet hdisjoint
  have hcompact : IsCompact K :=
    hB.of_isClosed_subset hpoly.isClosed (hsub.trans interior_subset)
  exact ⟨K, hcompact, hconv, hpoly, hx0, hsub, fun _ => Iff.rfl⟩

/-- A zero slope active at the initial point supplies the ceiling level.
Excluding zero active slopes on the boundary gives all geometric conclusions. -/
lemma compact_polyhedron_of_zero_active_slope {ι : Type uIota} [Fintype ι]
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (j0 : ι)
    (B : Set (Fin d → ℝ)) (x0 : Fin d → ℝ)
    (hB : IsCompact B) (hx0B : x0 ∈ interior B)
    (hzero : a j0 = 0)
    (hactive0 : ∀ j, dot (a j0) x0 + c j0 ≤ dot (a j) x0 + c j)
    (hboundary : ∀ x ∈ frontier B, ∀ j,
      (∀ k, dot (a j) x + c j ≤ dot (a k) x + c k) → a j ≠ 0) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ Convex ℝ K ∧
      IsFinitePolyhedron K ∧ x0 ∈ K ∧ K ⊆ interior B ∧
      ∀ x, x ∈ K ↔ ∀ j, c j0 ≤ dot (a j) x + c j := by
  apply compact_polyhedron_of_affine_barriers a c (c j0) B x0 hB hx0B
  · intro j
    simpa only [hzero, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      using hactive0 j
  · intro x hxB
    classical
    by_contra hnot
    push Not at hnot
    have hj0active : ∀ k, dot (a j0) x + c j0 ≤ dot (a k) x + c k := by
      intro k
      simpa only [hzero, dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
        using hnot k
    exact hboundary x hxB j0 hj0active hzero

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem326.Affine

/-- The superlevel set of every member of a finite affine family. -/
def labelPolytope {d : ℕ} (Λ : Finset (Label d)) (h M : ℝ) :
    Set (Fin d → ℝ) := {x | ∀ L ∈ Λ, M ≤ L.value h x}

lemma labelPolytope_isFinitePolyhedron {d : ℕ}
    (Λ : Finset (Label d)) (h M : ℝ) : IsFinitePolyhedron (labelPolytope Λ h M) := by
  classical
  have hpoly := finiteAffine_superlevel_isFinitePolyhedron
    (fun L : Λ => L.val.slope) (fun L : Λ => L.val.offset h) M
  convert hpoly using 1
  ext x
  simp only [labelPolytope, Set.mem_ofPred_eq, Subtype.forall, Label.value, dot]

lemma labelPolytope_active_iff {d : ℕ} {Λ : Finset (Label d)}
    {h : ℝ} {L0 L : Label d} {x : Fin d → ℝ}
    (hL0 : L0 ∈ Λ) (hzero : L0.slope = 0)
    (hx : x ∈ labelPolytope Λ h (L0.offset h)) :
    Active Λ L h x ↔ L ∈ Λ ∧ L.value h x = L0.offset h := by
  have hvalue : L0.value h x = L0.offset h := by simp [Label.value, hzero]
  constructor
  · intro ha
    exact ⟨ha.1, le_antisymm (by simpa only [hvalue] using ha.2 L0 hL0) (hx L ha.1)⟩
  · rintro ⟨hL, hLeq⟩
    exact ⟨hL, fun J hJ => hLeq ▸ hx J hJ⟩

/-- The geometric part of the affine trapping construction, with the canonical
label and activity definitions. Only the activity certificates are assumed;
no differential equation or global-solution assertion is used. -/
lemma exists_compact_labelPolytope {d : ℕ}
    (Λ : Finset (Label d)) (hne : Λ.Nonempty) (h : ℝ)
    (B : Set (Fin d → ℝ)) (x0 : Fin d → ℝ)
    (hB : IsCompact B) (hx0B : x0 ∈ interior B)
    (hinitial : ∀ L, Active Λ L h x0 → L.slope = 0)
    (hboundary : ∀ x ∈ frontier B, ∀ L, Active Λ L h x → L.slope ≠ 0) :
    ∃ L0, Active Λ L0 h x0 ∧ L0.slope = 0 ∧
      IsCompact (labelPolytope Λ h (L0.offset h)) ∧
      Convex ℝ (labelPolytope Λ h (L0.offset h)) ∧
      IsFinitePolyhedron (labelPolytope Λ h (L0.offset h)) ∧
      x0 ∈ labelPolytope Λ h (L0.offset h) ∧
      labelPolytope Λ h (L0.offset h) ⊆ interior B := by
  classical
  obtain ⟨L0, hact⟩ := exists_active Λ hne h x0
  have hzero := hinitial L0 hact
  have hpoly := labelPolytope_isFinitePolyhedron Λ h (L0.offset h)
  have hconv := hpoly.convex
  have hvalue : L0.value h x0 = L0.offset h := by simp [Label.value, hzero]
  have hx0 : x0 ∈ labelPolytope Λ h (L0.offset h) := by
    intro L hL
    simpa only [hvalue] using hact.2 L hL
  have hdisjoint : Disjoint (labelPolytope Λ h (L0.offset h)) (frontier B) := by
    rw [Set.disjoint_left]
    intro x hx hxB
    have hactx : Active Λ L0 h x :=
      (labelPolytope_active_iff hact.1 hzero hx).2
        ⟨hact.1, by simp [Label.value, hzero]⟩
    exact hboundary x hxB L0 hactx hzero
  have hsub : labelPolytope Λ h (L0.offset h) ⊆ interior B :=
    Geometry.subset_interior_of_disjoint_frontier hconv.isPreconnected
      ⟨x0, hx0, hx0B⟩ hdisjoint
  have hcompact : IsCompact (labelPolytope Λ h (L0.offset h)) :=
    hB.of_isClosed_subset hpoly.isClosed (hsub.trans interior_subset)
  exact ⟨L0, hact, hzero, hcompact, hconv, hpoly, hx0, hsub⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326.Affine

open scoped BigOperators

/-- The elementary sup-norm / one-norm pairing estimate used by active affine labels. -/
theorem abs_sum_mul_le (ι : Type uIota) [Fintype ι]
    (u v : ι → ℝ) :
    |∑ i, u i * v i| ≤ ‖u‖ * ∑ i, |v i| := by
  classical
  calc
    |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |v i| := by simp only [abs_mul]
    _ ≤ ∑ i, ‖u‖ * |v i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i) (abs_nonneg _)
    _ = ‖u‖ * ∑ i, |v i| := by rw [Finset.mul_sum]

/-- A nonzero linear comparison is stable under an error smaller than half its gap. -/
theorem sign_gap_of_abs_sub_lt {a b H : ℝ}
    (hab : |a - b| < |b| / 2) (hH : H ≤ |b| / 2) :
    (0 < a ↔ 0 < b) ∧ (a < 0 ↔ b < 0) ∧ H ≤ |a| := by
  have hb : b ≠ 0 := by
    intro h
    simp only [h, abs_zero, zero_div] at hab
    exact (not_lt_of_ge (abs_nonneg _)) hab
  rcases lt_or_gt_of_ne hb with hb | hb
  · rw [abs_of_neg hb] at hab hH
    have ha : a < 0 := by
      have h := (abs_lt.mp hab).2
      linarith
    constructor
    · simp [not_lt_of_ge ha.le, not_lt_of_ge hb.le]
    constructor
    · simp [ha, hb]
    · rw [abs_of_neg ha]
      have h := (abs_lt.mp hab).2
      linarith
  · rw [abs_of_pos hb] at hab hH
    have ha : 0 < a := by
      have h := (abs_lt.mp hab).1
      linarith
    constructor
    · simp [ha, hb]
    constructor
    · simp [not_lt_of_ge ha.le, not_lt_of_ge hb.le]
    · rw [abs_of_pos ha]
      have h := (abs_lt.mp hab).1
      linarith

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Filter
open scoped Topology

namespace Problem326

/-- A finite minimum has nonnegative lower right slope when every active
branch has a nonnegative right derivative. Inactive branches need only be
right-continuous. -/
theorem eventually_slope_finset_inf'_gt
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {x : ℝ}
    (hc : ∀ i ∈ s, ContinuousWithinAt (f i) (Ioi x) x)
    (hd : ∀ i ∈ s, f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivWithinAt (f i) v (Ici x) x)
    {r : ℝ} (hr : r < 0) :
    ∀ᶠ y in 𝓝[>] x,
      r < slope (fun t => s.inf' hs (fun i => f i t)) x y := by
  have hi : ∀ i ∈ s, ∀ᶠ y in 𝓝[>] x,
      s.inf' hs (fun j => f j x) + r * (y - x) < f i y := by
    intro i his
    have hle : s.inf' hs (fun j => f j x) ≤ f i x :=
      Finset.inf'_le _ his
    rcases hle.eq_or_lt with heq | hlt
    · obtain ⟨v, hv, hvd⟩ := hd i his heq.symm
      have hslope : ∀ᶠ y in 𝓝[>] x, r < slope (f i) x y :=
        (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1
          hvd.Ioi_of_Ici (Ioi_mem_nhds (lt_of_lt_of_le hr hv))
      filter_upwards [hslope, eventually_mem_nhdsWithin] with y hy hxy
      rw [slope_def_field] at hy
      have hm := (lt_div_iff₀ (sub_pos.mpr hxy)).mp hy
      rw [heq]
      linarith
    · have hc' : ∀ᶠ y in 𝓝[>] x, s.inf' hs (fun j => f j x) < f i y :=
        hc i his (Ioi_mem_nhds hlt)
      filter_upwards [hc', eventually_mem_nhdsWithin] with y hy hxy
      have hm : r * (y - x) < 0 := mul_neg_of_neg_of_pos hr (sub_pos.mpr hxy)
      linarith
  have hall := (s.eventually_all).mpr hi
  filter_upwards [hall, eventually_mem_nhdsWithin] with y hy hxy
  have hm : s.inf' hs (fun j => f j x) + r * (y - x) <
      s.inf' hs (fun i => f i y) := (Finset.lt_inf'_iff hs).mpr hy
  rw [slope_def_field]
  apply (lt_div_iff₀ (sub_pos.mpr hxy)).mpr
  linarith

/-- Endpoint comparison for a finite minimum, using only derivatives of active
branches. The right derivative is required at the left endpoint. -/
theorem finset_inf'_initial_le
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s,
      f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivWithinAt (f i) v (Ici x) x) :
    ∀ t ∈ Icc a b, s.inf' hs (fun i => f i a) ≤ s.inf' hs (fun i => f i t) := by
  let F : ℝ → ℝ := fun t => s.inf' hs (fun i => f i t)
  have hFc : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hs hc
  have hfence : ∀ t ∈ Icc a b, -F t ≤ -F a := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hFc.neg (le_refl (-F a))
      continuousOn_const (B' := fun _ => 0)
    · intro x hx
      exact (hasDerivAt_const x (-F a)).hasDerivWithinAt
    · intro x hx r hr
      have hlocal := eventually_slope_finset_inf'_gt hs
        (fun i hi => (hc i hi x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hx))
        (hd x hx) (neg_neg_of_pos hr)
      apply Filter.Eventually.frequently
      filter_upwards [hlocal] with y hy
      change slope (fun t => -F t) x y < r
      rw [slope_neg]
      change -r < slope F x y at hy
      linarith
  intro t ht
  exact neg_le_neg_iff.mp (hfence t ht)

/-- A finite minimum is monotone when every active branch has nonnegative
right derivative. No derivative is required of an inactive branch. -/
theorem monotoneOn_finset_inf'_of_active_right_deriv_nonneg
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s,
      f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivWithinAt (f i) v (Ici x) x) :
    MonotoneOn (fun t => s.inf' hs (fun i => f i t)) (Icc a b) := by
  intro u hu v hv huv
  apply finset_inf'_initial_le hs
    (fun i hi => (hc i hi).mono (Icc_subset_Icc hu.1 hv.2))
    (fun x hx => hd x ⟨hu.1.trans hx.1, hx.2.trans_le hv.2⟩)
    v ⟨huv, le_refl v⟩

/-- Interior-derivative form: continuity handles both endpoints, so this applies
to solution curves whose ODE is only assumed on an open interval. -/
theorem monotoneOn_finset_inf'_of_active_deriv_nonneg
    {ι : Type uIota} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∀ i ∈ s,
      f i x = s.inf' hs (fun j => f j x) →
      ∃ v : ℝ, 0 ≤ v ∧ HasDerivAt (f i) v x) :
    MonotoneOn (fun t => s.inf' hs (fun i => f i t)) (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_refl _
  let F : ℝ → ℝ := fun t => s.inf' hs (fun i => f i t)
  have hFc : ContinuousOn F (Icc a b) := ContinuousOn.finset_inf'_apply hs hc
  have hclosure : u ∈ closure (Ioo u v) := by
    rw [closure_Ioo huv.ne]
    exact ⟨le_refl u, huv.le⟩
  have hsub : Ioo u v ⊆ Icc a b := by
    intro y hy
    exact ⟨hu.1.trans hy.1.le, hy.2.le.trans hv.2⟩
  apply ContinuousWithinAt.closure_le hclosure
    ((hFc u hu).mono hsub) continuousWithinAt_const
  intro y hy
  apply finset_inf'_initial_le hs
    (fun i hi => (hc i hi).mono (Icc_subset_Icc (hu.1.trans hy.1.le) hv.2))
    ?_ v ⟨hy.2.le, le_refl v⟩
  intro x hx i hi hactive
  obtain ⟨w, hw, hwd⟩ := hd x
    ⟨lt_of_le_of_lt hu.1 (hy.1.trans_le hx.1), hx.2.trans_le hv.2⟩ i hi hactive
  exact ⟨w, hw, hwd.hasDerivWithinAt⟩

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set

namespace Problem326

/-- Differentiation of a fixed linear functional along a state-space curve. -/
theorem hasDerivAt_dot_curve {d : ℕ} (a : Fin d → ℝ)
    {x : ℝ → (Fin d → ℝ)} {v : Fin d → ℝ} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun u => dot a (x u)) (dot a v) t := by
  unfold dot
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pi.mp hx i).const_mul (a i)

/-- Fixed affine functionals preserve continuity on a time interval. -/
theorem continuousOn_dot_curve {d : ℕ} (a : Fin d → ℝ)
    {x : ℝ → (Fin d → ℝ)} {S : Set ℝ} (hx : ContinuousOn x S) :
    ContinuousOn (fun t => dot a (x t)) S := by
  unfold dot
  fun_prop

/-- An active inward-pointing condition makes a finite affine minimum
nondecreasing along any differentiable curve in the specified region. -/
theorem affineMinimum_monotoneOn
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {u v : ℝ}
    (hx : ContinuousOn x (Icc u v))
    (hxd : ∀ t ∈ Ioo u v, HasDerivAt x (f (x t)) t)
    (hB : ∀ t ∈ Icc u v, x t ∈ B)
    (hinward : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = s.inf' hs (fun j => dot (a j) z + c j) →
      0 ≤ dot (a i) (f z)) :
    MonotoneOn (fun t => s.inf' hs (fun i => dot (a i) (x t) + c i)) (Icc u v) := by
  apply monotoneOn_finset_inf'_of_active_deriv_nonneg hs
  · intro i hi
    exact (continuousOn_dot_curve (a i) hx).add continuousOn_const
  · intro t ht i hi hactive
    refine ⟨dot (a i) (f (x t)), hinward (x t) (hB t (Ioo_subset_Icc_self ht))
      i hi hactive, ?_⟩
    exact (hasDerivAt_dot_curve (a i) (hxd t ht)).add_const (c i)

/-- The maximum-level plateau is preserved along a solution segment in the
region where all active affine branches point inward. -/
theorem affineMinimum_eq_of_ceiling
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {u v M : ℝ}
    (hx : ContinuousOn x (Icc u v))
    (hxd : ∀ t ∈ Ioo u v, HasDerivAt x (f (x t)) t)
    (hB : ∀ t ∈ Icc u v, x t ∈ B)
    (hinward : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = s.inf' hs (fun j => dot (a j) z + c j) →
      0 ≤ dot (a i) (f z))
    (hceiling : ∀ z ∈ B, s.inf' hs (fun i => dot (a i) z + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) (x u) + c i) = M) :
    ∀ t ∈ Icc u v, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  intro t ht
  apply le_antisymm (hceiling (x t) (hB t ht))
  rw [← hstart]
  exact affineMinimum_monotoneOn s hs a c f B hx hxd hB hinward
    ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

/-- Exact finite-forward-solution specialization of affine plateau preservation. -/
theorem IsForwardSolutionOn.affineMinimum_eq
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {z : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardSolutionOn N κ z T x)
    {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (B : Set (Fin d → ℝ)) {M : ℝ}
    (hB : ∀ t ∈ Icc 0 T, x t ∈ B)
    (hinward : ∀ y ∈ B, ∀ i ∈ s,
      dot (a i) y + c i = s.inf' hs (fun j => dot (a j) y + c j) →
      0 ≤ dot (a i) (massAction N κ y))
    (hceiling : ∀ y ∈ B, s.inf' hs (fun i => dot (a i) y + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) z + c i) = M) :
    ∀ t ∈ Icc 0 T, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  apply affineMinimum_eq_of_ceiling s hs a c (massAction N κ) B
    hx.2.1 hx.2.2 hB hinward hceiling
  simpa [hx.1] using hstart

/-- A finite affine plateau traps any solution segment, without an a priori
assumption that the segment stays in the region. The first-boundary argument
uses the active inward estimate only inside the closed region. -/
theorem affineMinimum_trapped
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {T M : ℝ}
    (hT : 0 ≤ T) (hclosed : IsClosed B)
    (hx : ContinuousOn x (Icc 0 T))
    (hxd : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hx0 : x 0 ∈ interior B)
    (hinward : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = s.inf' hs (fun j => dot (a j) z + c j) →
      0 ≤ dot (a i) (f z))
    (hceiling : ∀ z ∈ B, s.inf' hs (fun i => dot (a i) z + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) (x 0) + c i) = M)
    (hboundary : ∀ z ∈ frontier B,
      s.inf' hs (fun i => dot (a i) z + c i) ≠ M) :
    MapsTo x (Icc 0 T) (interior B) ∧
      ∀ t ∈ Icc 0 T, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  have hstay : MapsTo x (Icc 0 T) (interior B) := by
    apply Geometry.mapsTo_interior_of_no_first_boundary hT hclosed hx hx0
    intro τ hτ hseg hfront
    have hsub : Icc 0 τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτ.2
    have heq := affineMinimum_eq_of_ceiling s hs a c f B (hx.mono hsub)
      (fun t ht => hxd t ⟨ht.1, ht.2.trans_le hτ.2⟩)
      hseg hinward hceiling hstart τ ⟨hτ.1, le_rfl⟩
    exact hboundary (x τ) hfront heq
  refine ⟨hstay, ?_⟩
  exact affineMinimum_eq_of_ceiling s hs a c f B hx hxd
    (fun t ht => interior_subset (hstay ht)) hinward hceiling hstart

/-- Exact mass-action specialization of the finite-interval trapping theorem. -/
theorem IsForwardSolutionOn.affineMinimum_trapped
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {z : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardSolutionOn N κ z T x)
    {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (B : Set (Fin d → ℝ)) {M : ℝ}
    (hT : 0 ≤ T) (hclosed : IsClosed B) (hz : z ∈ interior B)
    (hinward : ∀ y ∈ B, ∀ i ∈ s,
      dot (a i) y + c i = s.inf' hs (fun j => dot (a j) y + c j) →
      0 ≤ dot (a i) (massAction N κ y))
    (hceiling : ∀ y ∈ B, s.inf' hs (fun i => dot (a i) y + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) z + c i) = M)
    (hboundary : ∀ y ∈ frontier B,
      s.inf' hs (fun i => dot (a i) y + c i) ≠ M) :
    MapsTo x (Icc 0 T) (interior B) ∧
      ∀ t ∈ Icc 0 T, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  apply Problem326.affineMinimum_trapped s hs a c (massAction N κ) B
    hT hclosed hx.2.1 hx.2.2
  · simpa [hx.1] using hz
  · exact hinward
  · exact hceiling
  · simpa [hx.1] using hstart
  · exact hboundary

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators
open Filter Topology

namespace Problem326

-- The existence form avoids imposing any continuity on the chosen tolerance.
theorem exists_sign_tolerance {d : ℕ} (D : Finset (Fin d → ℝ))
    (r : Fin d → ℝ) :
    ∃ E : ℝ, 0 < E ∧ E ≤ 1 / 2 ∧
      ∀ p : Fin d → ℝ, (∀ i, |p i - r i| < E) →
        ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
          |(∑ i, p i * v i) - (∑ i, r i * v i)| <
            |∑ i, r i * v i| / 2 := by
  classical
  have hnear : ∀ᶠ p : Fin d → ℝ in 𝓝 r,
      ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
        |(∑ i, p i * v i) - (∑ i, r i * v i)| <
          |∑ i, r i * v i| / 2 := by
    apply (Filter.eventually_all_finset D).2
    intro v hv
    by_cases hz : (∑ i, r i * v i) = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hz).elim)
    · have hc : Continuous (fun p : Fin d → ℝ =>
          |(∑ i, p i * v i) - (∑ i, r i * v i)|) := by
        fun_prop
      have hp : (0 : ℝ) < |∑ i, r i * v i| / 2 :=
        div_pos (abs_pos.mpr hz) (by norm_num)
      have he := (hc.continuousAt (x := r)).eventually_lt_const
        (show |(∑ i, r i * v i) - (∑ i, r i * v i)| <
          |∑ i, r i * v i| / 2 by simpa using hp)
      exact he.mono (fun p h _ => h)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro p hp
  apply hball
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro i
  rw [Real.dist_eq]
  exact (hp i).trans_le (min_le_left _ _)

/-- A perturbation smaller than half a nonzero value preserves its sign and half-gap. -/
theorem sign_and_half_gap_of_abs_sub_lt {p r : ℝ} (hr : r ≠ 0)
    (hclose : |p - r| < |r| / 2) :
    (0 < p ↔ 0 < r) ∧ (p < 0 ↔ r < 0) ∧ |r| / 2 < |p| := by
  rcases lt_or_gt_of_ne hr with hr | hr
  · rw [abs_of_neg hr] at hclose
    have hb := abs_lt.mp hclose
    have hp : p < 0 := by linarith [hb.2]
    refine ⟨iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge hr.le),
      iff_of_true hp hr, ?_⟩
    rw [abs_of_neg hp, abs_of_neg hr]
    linarith [hb.2]
  · rw [abs_of_pos hr] at hclose
    have hb := abs_lt.mp hclose
    have hp : 0 < p := by linarith [hb.1]
    refine ⟨iff_of_true hp hr,
      iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge hr.le), ?_⟩
    rw [abs_of_pos hp, abs_of_pos hr]
    linarith [hb.1]

/-- Any finite family of positive real numbers has a common positive lower bound. -/
theorem finite_positive_lower_bound {α : Type uAlpha} (S : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ a ∈ S, H ≤ f a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨H, hH, hHone, hHf⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
      refine ⟨min H (f a), lt_min hH (hf a (Finset.mem_insert_self _ _)),
        (min_le_left _ _).trans hHone, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hHf b hb)

/-- In a fixed finite slope family, all nonzero comparisons have a uniform half-gap. -/
theorem exists_uniform_dot_gap {d : ℕ} (R D : Finset (Fin d → ℝ)) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧
      ∀ r ∈ R, ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
        H ≤ |∑ i, r i * v i| / 2 := by
  classical
  let S := (R.product D).filter (fun rv => (∑ i, rv.1 i * rv.2 i) ≠ 0)
  obtain ⟨H, hH, hHone, hHgap⟩ := finite_positive_lower_bound S
    (fun rv => |∑ i, rv.1 i * rv.2 i| / 2) (by
      intro rv hrv
      exact div_pos (abs_pos.mpr (Finset.mem_filter.mp hrv).2) (by norm_num))
  refine ⟨H, hH, hHone, ?_⟩
  intro r hr v hv hne
  exact hHgap (r, v) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr, hv⟩, hne⟩)

/-- The tolerance can be selected pointwise; no regularity of it is required. -/
theorem exists_sign_tolerance_function {d : ℕ} (D : Finset (Fin d → ℝ)) :
    ∃ E : (Fin d → ℝ) → ℝ,
      (∀ r, 0 < E r ∧ E r ≤ 1 / 2) ∧
      ∀ r p : Fin d → ℝ, (∀ i, |p i - r i| < E r) →
        ∀ v ∈ D, (∑ i, r i * v i) ≠ 0 →
          (0 < (∑ i, p i * v i) ↔ 0 < (∑ i, r i * v i)) ∧
          ((∑ i, p i * v i) < 0 ↔ (∑ i, r i * v i) < 0) ∧
          |∑ i, r i * v i| / 2 < |∑ i, p i * v i| := by
  choose E hEpos hEbound hEclose using exists_sign_tolerance D
  refine ⟨E, fun r => ⟨hEpos r, hEbound r⟩, ?_⟩
  intro r p hp v hv hne
  exact sign_and_half_gap_of_abs_sub_lt hne (hEclose r p hp v hv hne)

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open Filter Topology
open scoped BigOperators

namespace Problem326

/-- The final small parameter is chosen only after the positive gap is fixed.
The rate type may be empty; the rate inequalities are then vacuous. -/
theorem exists_small_parameter {ι : Type uIota} {η : Type uEta} [Fintype ι] [Fintype η]
    (c : ι → ℝ) (κ : η → ℝ) {H h₀ : ℝ}
    (hH : 0 < H) (hh₀ : 0 < h₀) (hκ : ∀ e, 0 < κ e) :
    ∃ h : ℝ, 0 < h ∧ h < h₀ ∧ h < 1 ∧
      (∀ i, |c i / Real.log h| < H) ∧
      ∀ e, h ^ H * (∑ e, κ e) < κ e := by
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < h₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hh₀)
  have hone : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have hlogs : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i, |c i / Real.log h| < H := by
    apply Filter.eventually_all.2
    intro i
    have ht : Tendsto (fun h : ℝ => |c i / Real.log h|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.tendsto_log_nhdsGT_zero.const_div_atBot (c i)).abs
    exact ht.eventually_lt_const hH
  have hrates : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ e, h ^ H * (∑ e, κ e) < κ e := by
    apply Filter.eventually_all.2
    intro e
    have hpow : Tendsto (fun h : ℝ => h ^ H) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.rpow_const_nhds_zero hH
    have ht : Tendsto (fun h : ℝ => h ^ H * (∑ e, κ e)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hpow.mul_const (∑ e, κ e)
    exact ht.eventually_lt_const (hκ e)
  exact (hpositive.and (hsmall.and (hone.and (hlogs.and hrates)))).exists

/-- Logarithmic coordinates reconstruct a positive state for a base in `(0,1)`. -/
theorem rpow_log_ratio {h x : ℝ} (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    h ^ (Real.log x / Real.log h) = x := by
  rw [Real.rpow_def_of_pos hh]
  have hlog : Real.log h ≠ 0 := ne_of_lt (Real.log_neg hh hh1)
  rw [mul_div_cancel₀ _ hlog, Real.exp_log hx]

/-- Simultaneous initial-exponent and rate separation with explicit reconstruction. -/
theorem exists_initial_exponent_parameter {ι : Type uIota} {η : Type uEta} [Fintype ι] [Fintype η]
    (x₀ : ι → ℝ) (κ : η → ℝ) {H h₀ : ℝ}
    (hx₀ : ∀ i, 0 < x₀ i) (hH : 0 < H) (hh₀ : 0 < h₀) (hκ : ∀ e, 0 < κ e) :
    ∃ (h : ℝ) (p : ι → ℝ), 0 < h ∧ h < h₀ ∧ h < 1 ∧
      (∀ i, |p i| < H) ∧ (∀ i, h ^ (p i) = x₀ i) ∧
      ∀ e, h ^ H * (∑ e, κ e) < κ e := by
  obtain ⟨h, hh, hh₀', hh1, hp, hrates⟩ :=
    exists_small_parameter (fun i => Real.log (x₀ i)) κ hH hh₀ hκ
  refine ⟨h, fun i => Real.log (x₀ i) / Real.log h, hh, hh₀', hh1, hp, ?_, hrates⟩
  intro i
  exact rpow_log_ratio hh hh1 (hx₀ i)

end Problem326

/-! Simultaneous small-parameter choice for the affine trapping construction. -/

namespace Problem326

open Filter Set
open scoped Topology

/-- The logarithmic exponent of a fixed coordinate tends to zero when the
base tends to zero from the right.  Positivity of the coordinate is not
needed for this limit (but is needed to reconstruct it from its exponent). -/
theorem tendsto_log_coordinate_div_log (x : ℝ) :
    Tendsto (fun h : ℝ => Real.log x / Real.log h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log x)

/-- A positive fixed power tends to zero, including on the positive side. -/
theorem tendsto_positive_rpow_nhdsGT_zero {H : ℝ} (hH : 0 < H) :
    Tendsto (fun h : ℝ => h ^ H) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [Real.zero_rpow hH.ne'] using
    (Real.continuousAt_rpow_const 0 H (Or.inr hH.le)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))

/-- Choose one small parameter after all slopes and their positive separation
have already been fixed.  All coordinate and reaction constraints hold
simultaneously; an empty reaction type causes no exceptional case. -/
theorem exists_small_parameter_for_rates
    {ι : Type uIota} {E : Type uE} [Finite ι] [Fintype E]
    (x0 : ι → ℝ) (κ : E → ℝ) {h0 H : ℝ}
    (hh0 : 0 < h0) (hH : 0 < H) (hκ : ∀ e, 0 < κ e) :
    ∃ h : ℝ, 0 < h ∧ h < h0 ∧ h < 1 ∧
      (∀ i, |Real.log (x0 i) / Real.log h| < H) ∧
      (∀ e, h ^ H * (∑ f, κ f) < κ e) := by
  have hcoords : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ i, |Real.log (x0 i) / Real.log h| < H := by
    apply eventually_all.mpr
    intro i
    have hlim := (tendsto_log_coordinate_div_log (x0 i)).abs
    have hevent := hlim.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hH))
    simpa only [abs_zero, mem_Iio] using hevent
  have hrates : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ e, h ^ H * (∑ f, κ f) < κ e := by
    apply eventually_all.mpr
    intro e
    have hlim := (tendsto_positive_rpow_nhdsGT_zero hH).mul_const (∑ f, κ f)
    have hevent := hlim.eventually (Iio_mem_nhds (by simpa only [zero_mul] using hκ e))
    simpa only [zero_mul, mem_Iio] using hevent
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < h0 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hh0)
  have hone : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  exact (hpositive.and (hsmall.and (hone.and (hcoords.and hrates)))).exists

/-- Positive coordinates are recovered exactly from their logarithmic
exponents for a base strictly between zero and one. -/
theorem rpow_log_coordinate {h x : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    h ^ (Real.log x / Real.log h) = x := by
  simpa only [Real.logb] using Real.rpow_logb hh hh1.ne hx

/-- The open symmetric exponent interval describes the interior of the
positive reciprocal box in each coordinate. -/
theorem abs_log_coordinate_lt_one_iff {h x : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    |Real.log x / Real.log h| < 1 ↔ h < x ∧ x < h⁻¹ := by
  rw [abs_lt]
  change (-1 < Real.logb h x ∧ Real.logb h x < 1) ↔ _
  rw [Real.lt_logb_iff_rpow_lt_of_base_lt_one hh hh1 hx,
    Real.logb_lt_iff_lt_rpow_of_base_lt_one hh hh1 hx]
  simp only [Real.rpow_neg_one, Real.rpow_one, and_comm]

/-- The closed symmetric exponent interval describes the closed positive
reciprocal box in each coordinate. -/
theorem abs_log_coordinate_le_one_iff {h x : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : 0 < x) :
    |Real.log x / Real.log h| ≤ 1 ↔ h ≤ x ∧ x ≤ h⁻¹ := by
  rw [abs_le]
  change (-1 ≤ Real.logb h x ∧ Real.logb h x ≤ 1) ↔ _
  rw [Real.le_logb_iff_rpow_le_of_base_lt_one hh hh1 hx,
    Real.logb_le_iff_le_rpow_of_base_lt_one hh hh1 hx]
  simp only [Real.rpow_neg_one, Real.rpow_one, and_comm]

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326Aux

/-- A perturbation by less than half the absolute value preserves the sign
and leaves a quantitative gap from zero. -/
theorem sign_gap_of_abs_sub_lt {a b : ℝ}
    (h : |a - b| < |b| / 2) :
    (0 < b → 0 < a ∧ b / 2 < a) ∧
    (b < 0 → a < 0 ∧ a < b / 2) ∧ |b| / 2 < |a| := by
  have hsub := abs_lt.mp h
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [abs_of_neg hb] at hsub
    have ha : a < 0 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · intro hb'
      linarith
    · intro _
      exact ⟨ha, by linarith⟩
    · rw [abs_of_neg hb, abs_of_neg ha]
      linarith
  · subst b
    simp only [abs_zero, zero_div] at h
    exact False.elim (not_lt_of_ge (abs_nonneg _) h)
  · rw [abs_of_pos hb] at hsub
    have ha : 0 < a := by linarith
    refine ⟨?_, ?_, ?_⟩
    · intro _
      exact ⟨ha, by linarith⟩
    · intro hb'
      linarith
    · rw [abs_of_pos hb, abs_of_pos ha]
      linarith

/-- Bounding each coordinate perturbation bounds any finite scalar product. -/
theorem abs_sum_mul_le {ι : Type uIota} [Fintype ι]
    (p r v : ι → ℝ) (E : ℝ)
    (h : ∀ i, |p i - r i| ≤ E) :
    |∑ i, (p i - r i) * v i| ≤ E * ∑ i, |v i| := by
  calc
    |∑ i, (p i - r i) * v i| ≤ ∑ i, |(p i - r i) * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |p i - r i| * |v i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, E * |v i| := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
    _ = E * ∑ i, |v i| := (Finset.mul_sum _ _ _).symm

/-- Monomials at exponential coordinates have the expected scalar exponent. -/
theorem prod_rpow_pow_eq {ι : Type uIota} [Fintype ι]
    {h : ℝ} (hh : 0 < h) (p : ι → ℝ) (y : ι → ℕ) :
    (∏ i, (h ^ (p i)) ^ (y i)) = h ^ (∑ i, p i * (y i : ℝ)) := by
  rw [Real.rpow_sum_of_pos hh]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.rpow_mul_natCast hh.le (p i) (y i)).symm

/-- An exponent gap orders monomials quantitatively when the base is below one. -/
theorem prod_rpow_pow_le_of_gap {ι : Type uIota} [Fintype ι]
    {h H : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (p : ι → ℝ) (y z : ι → ℕ)
    (hgap : H ≤ ∑ i, p i * ((z i : ℝ) - (y i : ℝ))) :
    (∏ i, (h ^ (p i)) ^ (z i)) ≤
      h ^ H * (∏ i, (h ^ (p i)) ^ (y i)) := by
  rw [prod_rpow_pow_eq hh, prod_rpow_pow_eq hh, ← Real.rpow_add hh]
  apply Real.rpow_le_rpow_of_exponent_ge hh hh1
  simp_rw [mul_sub] at hgap
  rw [Finset.sum_sub_distrib] at hgap
  linarith

/-- A finite collection of positive thresholds admits a common positive bound,
including when the indexing set is empty. -/
theorem exists_positive_common_bound {ι : Type uIota} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) {C : ℝ} (hC : 0 < C) :
    ∃ E : ℝ, 0 < E ∧ E ≤ C ∧ ∀ i ∈ s, E ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, hC, le_rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨E, hE, hEC, hEf⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min E (f a), lt_min hE (hf a (Finset.mem_insert_self _ _)),
      (min_le_left _ _).trans hEC, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hEf i hi)

/-- One tolerance controls all nonzero pairings with finitely many directions.
No continuity of the eventual tolerance as a function of `r` is required. -/
theorem exists_pairing_tolerance {ι : Type uIota} {J : Type uJ} [Fintype ι] [Fintype J]
    (r : ι → ℝ) (v : J → ι → ℝ) :
    ∃ E : ℝ, 0 < E ∧ E ≤ 1 / 2 ∧
      ∀ p : ι → ℝ, (∀ i, |p i - r i| ≤ E) →
      ∀ j, (∑ i, r i * v j i) ≠ 0 →
        |(∑ i, p i * v j i) - (∑ i, r i * v j i)| <
          |∑ i, r i * v j i| / 2 := by
  classical
  have hlocal : ∀ j : J, ∃ e : ℝ, 0 < e ∧
      ((∑ i, r i * v j i) ≠ 0 →
        (∑ i, |v j i|) * e < |∑ i, r i * v j i| / 2) := by
    intro j
    by_cases hj : (∑ i, r i * v j i) = 0
    · exact ⟨1, zero_lt_one, fun h => (h hj).elim⟩
    · obtain ⟨e, he, he'⟩ := exists_pos_mul_lt
        (half_pos (abs_pos.mpr hj)) (∑ i, |v j i|)
      exact ⟨e, he, fun _ => he'⟩
  choose e he he' using hlocal
  obtain ⟨E, hE, hEhalf, hEe⟩ := exists_positive_common_bound
    Finset.univ e (fun j _ => he j) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨E, hE, hEhalf, ?_⟩
  intro p hp j hj
  calc
    |(∑ i, p i * v j i) - (∑ i, r i * v j i)| =
        |∑ i, (p i - r i) * v j i| := by
          rw [← Finset.sum_sub_distrib]
          simp_rw [sub_mul]
    _ ≤ E * ∑ i, |v j i| := abs_sum_mul_le p r (v j) E hp
    _ ≤ e j * ∑ i, |v j i| := mul_le_mul_of_nonneg_right
      (hEe j (Finset.mem_univ j)) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    _ < |∑ i, r i * v j i| / 2 := by simpa [mul_comm] using he' j hj

/-- Finite nonzero pairings have a positive common quantitative gap. -/
theorem exists_positive_pairing_gap {J : Type uJ} [Fintype J] (a : J → ℝ) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ j, a j ≠ 0 → H ≤ |a j| / 2 := by
  classical
  let f : J → ℝ := fun j => if a j = 0 then 1 else |a j| / 2
  have hf : ∀ j, 0 < f j := by
    intro j
    dsimp [f]
    split_ifs with hj
    · norm_num
    · exact half_pos (abs_pos.mpr hj)
  obtain ⟨H, hH, hH1, hHf⟩ := exists_positive_common_bound
    Finset.univ f (fun j _ => hf j) zero_lt_one
  refine ⟨H, hH, hH1, ?_⟩
  intro j hj
  simpa [f, hj] using hHf j (Finset.mem_univ j)

end Problem326Aux

namespace Problem326

/-- Exact mass-action monomial representation at exponential coordinates. -/
theorem monomial_rpow {d : ℕ} {h : ℝ} (hh : 0 < h)
    (p : Fin d → ℝ) (y : Fin d → ℕ) :
    monomial (fun i => h ^ p i) y = h ^ (∑ i, p i * (y i : ℝ)) :=
  Problem326Aux.prod_rpow_pow_eq hh p y

/-- Exact monomial-order interface for active-slope sign-gap arguments. -/
theorem monomial_le_rpow_mul_of_gap {d : ℕ} {h H : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (p : Fin d → ℝ) (y z : Fin d → ℕ)
    (hgap : H ≤ ∑ i, p i * ((z i : ℝ) - (y i : ℝ))) :
    monomial (fun i => h ^ p i) z ≤ h ^ H * monomial (fun i => h ^ p i) y :=
  Problem326Aux.prod_rpow_pow_le_of_gap hh hh1 p y z hgap

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326

/-- Pairwise comparison formulation of activity in a finite affine family. -/
def AffineActive {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x : Fin d → ℝ) (j : Λ) : Prop :=
  ∀ k, dot (r j) x + c j ≤ dot (r k) x + c k

/-- Every finite nonempty affine family has an active label, including at ties. -/
theorem exists_affineActive {d : ℕ} {Λ : Type uLambda} [Fintype Λ] [Nonempty Λ]
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x : Fin d → ℝ) :
    ∃ j, AffineActive r c x j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
    (fun k => dot (r k) x + c k) Finset.univ_nonempty
  exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩

/-- Coordinate sign gaps force any initially active slope to vanish. -/
theorem affineActive_slope_eq_zero {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x p : Fin d → ℝ) {H : ℝ}
    (hp : ∀ i, |p i| < H)
    (hgap : ∀ j, AffineActive r c x j → ∀ i, r j i ≠ 0 → H ≤ |p i|)
    {j : Λ} (hj : AffineActive r c x j) : r j = 0 := by
  funext i
  by_contra hi
  exact (not_le_of_gt (hp i)) (hgap j hj i hi)

/-- The plateau cut out by a constant active branch contains the initial point.
This also records that plateau membership is exactly activity of that branch. -/
theorem constant_branch_plateau {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x₀ : Fin d → ℝ)
    {j : Λ} (hr : r j = 0) (hj : AffineActive r c x₀ j) :
    x₀ ∈ {x | ∀ k, c j ≤ dot (r k) x + c k} ∧
      ∀ x, (∀ k, c j ≤ dot (r k) x + c k) ↔ AffineActive r c x j := by
  have hz : ∀ x : Fin d → ℝ, dot (r j) x = 0 := by
    intro x
    simp [hr, dot]
  constructor
  · intro k
    simpa [hz] using hj k
  · intro x
    simp only [AffineActive, hz, zero_add]

/-- A zero-slope branch cannot be active at an exponent-box boundary point
when the active-label approximation has radius strictly below one there. -/
theorem constant_branch_not_active_on_boundary {d : ℕ} {Λ : Type uLambda}
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (X : (Fin d → ℝ) → (Fin d → ℝ))
    (E : (Fin d → ℝ) → ℝ) (hE : E 0 ≤ 1 / 2)
    {j : Λ} (hr : r j = 0) {p : Fin d → ℝ}
    (hboundary : ∃ i, |p i| = 1)
    (happrox : AffineActive r c (X p) j → ∀ i, |p i - r j i| < E (r j)) :
    ¬ AffineActive r c (X p) j := by
  intro hj
  obtain ⟨i, hi⟩ := hboundary
  have h := happrox hj i
  simp only [hr, Pi.zero_apply, sub_zero] at h
  linarith

/-- Combined algebraic certificate used before the geometric trapping step. -/
theorem exists_constant_plateau_certificate {d : ℕ} {Λ : Type uLambda}
    [Fintype Λ] [Nonempty Λ]
    (r : Λ → Fin d → ℝ) (c : Λ → ℝ) (x₀ p₀ : Fin d → ℝ) {H : ℝ}
    (hp₀ : ∀ i, |p₀ i| < H)
    (hgap : ∀ j, AffineActive r c x₀ j → ∀ i, r j i ≠ 0 → H ≤ |p₀ i|) :
    ∃ j : Λ, r j = 0 ∧
      x₀ ∈ {x | ∀ k, c j ≤ dot (r k) x + c k} ∧
      ∀ x, (∀ k, c j ≤ dot (r k) x + c k) ↔ AffineActive r c x j := by
  obtain ⟨j, hj⟩ := exists_affineActive r c x₀
  have hr := affineActive_slope_eq_zero r c x₀ p₀ hp₀ hgap hj
  exact ⟨j, hr, constant_branch_plateau r c x₀ hr hj⟩

end Problem326

end

end OAI
end
end

section
section
namespace OAI


/-! The weighted level difference is the integral of the flux over all
threshold cuts. This avoids choosing an ordering of the distinct levels. -/

namespace Problem326.CutFlux

open scoped BigOperators
open MeasureTheory

private theorem integrable_interval_indicator (a b q : ℝ) :
    Integrable ((Set.Ico a b).indicator (fun _ : ℝ => q)) := by
  apply (integrable_indicator_iff measurableSet_Ico).2
  exact integrableOn_const (by simp)

private theorem integral_signed_interval (a b q : ℝ) :
    (∫ c : ℝ, ((Set.Ico a b).indicator (fun _ : ℝ => q) c -
      (Set.Ico b a).indicator (fun _ : ℝ => q) c)) = q * (b - a) := by
  rw [integral_sub (integrable_interval_indicator a b q)
    (integrable_interval_indicator b a q)]
  simp only [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul]
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

/-- If every threshold cut has nonnegative net flux, then the weighted sum
of level differences is nonnegative. Edge weights can have either sign. -/
theorem weighted_difference_nonneg_of_threshold_flux {E : Type uE} [Fintype E]
    (s t q : E → ℝ)
    (hcut : ∀ c : ℝ,
      0 ≤ (∑ e ∈ Finset.univ.filter (fun e => s e ≤ c ∧ c < t e), q e) -
          (∑ e ∈ Finset.univ.filter (fun e => t e ≤ c ∧ c < s e), q e)) :
    0 ≤ ∑ e, q e * (t e - s e) := by
  classical
  let f : E → ℝ → ℝ := fun e c =>
    (Set.Ico (s e) (t e)).indicator (fun _ : ℝ => q e) c -
    (Set.Ico (t e) (s e)).indicator (fun _ : ℝ => q e) c
  have hf : ∀ e, Integrable (f e) := fun e =>
    (integrable_interval_indicator (s e) (t e) (q e)).sub
      (integrable_interval_indicator (t e) (s e) (q e))
  have hnonneg : ∀ c, 0 ≤ ∑ e, f e c := by
    intro c
    simpa only [f, Finset.sum_sub_distrib, Set.indicator_apply, Set.mem_Ico,
      Finset.sum_filter] using hcut c
  have hint : 0 ≤ ∫ c : ℝ, ∑ e, f e c := integral_nonneg (fun c => hnonneg c)
  rw [integral_finsetSum Finset.univ (fun e _ => hf e)] at hint
  simpa only [f, integral_signed_interval] using hint

end Problem326.CutFlux

end OAI
end
end

section
section
namespace OAI


/-! Finite directed-cut estimates used by the mass-action argument. -/

namespace Problem326.CutFlux

open scoped BigOperators

/-- A directed path leaving a set contains an edge leaving that set. -/
theorem transGen_crosses {V : Type uV} {r : V → V → Prop} {P : V → Prop}
    {u v : V} (h : Relation.TransGen r u v) (hu : P u) (hv : ¬ P v) :
    ∃ a b, r a b ∧ P a ∧ ¬ P b := by
  induction h with
  | single huv => exact ⟨_, _, huv, hu, hv⟩
  | @tail b c hab hbc ih =>
      by_cases hb : P b
      · exact ⟨b, c, hbc, hb, hv⟩
      · exact ih hb

/-- Every downward threshold crossing has an upward crossing when each edge
has a directed return path. No finiteness hypothesis is needed here. -/
theorem upward_of_downward {V : Type uV} {E : Type uE} (s t : E → V) (a : V → ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (c : ℝ) (e : E) (he : a (t e) ≤ c ∧ c < a (s e)) :
    ∃ f, a (s f) ≤ c ∧ c < a (t f) := by
  obtain ⟨u, v, huv, hu, hv⟩ :=
    transGen_crosses (P := fun z => a z ≤ c) (hreturn e) he.1
      (not_le.mpr he.2)
  obtain ⟨f, rfl, rfl⟩ := huv
  exact ⟨f, hu, lt_of_not_ge hv⟩

/-- The total upward flux across an ordered cut dominates the downward flux.
The rate assumption is phrased per edge, so it also handles an empty edge
set without introducing a minimum over the empty set. -/
theorem threshold_flux_nonneg_of_source_order {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ e f, a (s e) < a (s f) → w (s f) ≤ δ * w (s e))
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) (c : ℝ) :
    0 ≤ (∑ e ∈ Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e)),
          κ e * w (s e)) -
        (∑ e ∈ Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e)),
          κ e * w (s e)) := by
  classical
  let U := Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e))
  let D := Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e))
  change 0 ≤ (∑ e ∈ U, κ e * w (s e)) - ∑ e ∈ D, κ e * w (s e)
  have hnonneg : ∀ e, 0 ≤ κ e * w (s e) :=
    fun e => mul_nonneg (hκ e).le (hw (s e)).le
  by_cases hD : D.Nonempty
  · obtain ⟨e, he⟩ := hD
    have he' : a (t e) ≤ c ∧ c < a (s e) := (Finset.mem_filter.mp he).2
    obtain ⟨f, hf⟩ := upward_of_downward s t a hreturn c e he'
    have hfU : f ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
    have hweights : ∀ g ∈ D, w (s g) ≤ δ * w (s f) := by
      intro g hg
      have hg' := (Finset.mem_filter.mp hg).2
      exact horder f g (lt_of_le_of_lt hf.1 hg'.2)
    have hsumD : (∑ g ∈ D, κ g * w (s g)) ≤
        (δ * w (s f)) * (∑ g ∈ D, κ g) := by
      calc
        (∑ g ∈ D, κ g * w (s g)) ≤ ∑ g ∈ D, κ g * (δ * w (s f)) :=
          Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_left
            (hweights g hg) (hκ g).le
        _ = (δ * w (s f)) * (∑ g ∈ D, κ g) := by
          rw [← Finset.sum_mul, mul_comm]
    have hsumκ : (∑ g ∈ D, κ g) ≤ ∑ g, κ g := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        (fun g _ _ => (hκ g).le)
    have hdom : (∑ g ∈ D, κ g * w (s g)) < κ f * w (s f) := by
      calc
        (∑ g ∈ D, κ g * w (s g)) ≤
            (δ * w (s f)) * (∑ g ∈ D, κ g) := hsumD
        _ ≤ (δ * w (s f)) * (∑ g, κ g) :=
          mul_le_mul_of_nonneg_left hsumκ (mul_nonneg hδ (hw (s f)).le)
        _ < κ f * w (s f) := by
          nlinarith [mul_lt_mul_of_pos_right (hrate f) (hw (s f))]
    have hsingle : κ f * w (s f) ≤ ∑ g ∈ U, κ g * w (s g) :=
      Finset.single_le_sum (fun g _ => hnonneg g) hfU
    linarith
  · have hDe : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    rw [hDe, Finset.sum_empty, sub_zero]
    exact Finset.sum_nonneg fun e _ => hnonneg e

/-- The all-vertex version of the threshold flux inequality. -/
theorem threshold_flux_nonneg {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ u v, a u < a v → w v ≤ δ * w u)
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) (c : ℝ) :
    0 ≤ (∑ e ∈ Finset.univ.filter (fun e => a (s e) ≤ c ∧ c < a (t e)),
          κ e * w (s e)) -
        (∑ e ∈ Finset.univ.filter (fun e => a (t e) ≤ c ∧ c < a (s e)),
          κ e * w (s e)) := by
  exact threshold_flux_nonneg_of_source_order s t a w κ δ hreturn hw hκ hδ
    (fun e f => horder (s e) (s f)) hrate c

theorem total_flux_nonneg {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ u v, a u < a v → w v ≤ δ * w u)
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) :
    0 ≤ ∑ e, κ e * w (s e) * (a (t e) - a (s e)) := by
  apply weighted_difference_nonneg_of_threshold_flux
    (fun e => a (s e)) (fun e => a (t e)) (fun e => κ e * w (s e))
  exact threshold_flux_nonneg s t a w κ δ hreturn hw hκ hδ horder hrate

theorem total_flux_nonneg_of_source_order {V : Type uV} {E : Type uE} [Fintype E]
    (s t : E → V) (a w : V → ℝ) (κ : E → ℝ) (δ : ℝ)
    (hreturn : ∀ e, Relation.TransGen
      (fun u v => ∃ f, s f = u ∧ t f = v) (t e) (s e))
    (hw : ∀ v, 0 < w v) (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ e f, a (s e) < a (s f) → w (s f) ≤ δ * w (s e))
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) :
    0 ≤ ∑ e, κ e * w (s e) * (a (t e) - a (s e)) := by
  apply weighted_difference_nonneg_of_threshold_flux
    (fun e => a (s e)) (fun e => a (t e)) (fun e => κ e * w (s e))
  exact threshold_flux_nonneg_of_source_order s t a w κ δ hreturn hw hκ hδ horder hrate

end Problem326.CutFlux

end OAI
end
end

section
section
namespace OAI

/-! Application of the finite directed-cut inequality to the exact qualified
mass-action vector field. -/

noncomputable section

namespace Problem326

open scoped BigOperators

/-- Pairing the mass-action field with a normal gives the corresponding
weighted difference of complex levels. -/
theorem dot_massAction_eq_flux {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x r : Fin d → ℝ) :
    dot r (massAction N κ x) =
      ∑ e : Reaction N, κ e * monomial x e.val.1 *
        (dot r (fun i => (e.val.2 i : ℝ)) - dot r (fun i => (e.val.1 i : ℝ))) := by
  classical
  simp only [dot, massAction, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All-pairs monomial domination for the network supplies an inward
mass-action derivative in the specified direction. Positivity of species
and rates is the only analytical input to this finite estimate. -/
theorem massAction_inward_of_monomial_order {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x r : Fin d → ℝ) (δ : ℝ)
    (hweak : WeaklyReversible N) (hx : PositiveState x)
    (hκ : ∀ e, 0 < κ e) (hδ : 0 ≤ δ)
    (horder : ∀ y ∈ N.complexes, ∀ z ∈ N.complexes,
      dot r (fun i => (y i : ℝ)) < dot r (fun i => (z i : ℝ)) →
      monomial x z ≤ δ * monomial x y)
    (hrate : ∀ e, δ * (∑ f, κ f) < κ e) :
    0 ≤ dot r (massAction N κ x) := by
  classical
  rw [dot_massAction_eq_flux]
  apply CutFlux.total_flux_nonneg_of_source_order
    (fun e : Reaction N => e.val.1) (fun e : Reaction N => e.val.2)
    (fun y => dot r (fun i => (y i : ℝ))) (monomial x) κ δ
  · intro e
    apply Relation.TransGen.mono (r := HasReaction N) ?_ _ _ (hweak e)
    intro y z hyz
    exact ⟨⟨(y, z), hyz⟩, rfl, rfl⟩
  · intro y
    exact Finset.prod_pos fun i _ => pow_pos (hx i) (y i)
  · exact hκ
  · exact hδ
  · intro e f hef
    exact horder e.val.1 (N.source_mem e.val e.property)
      f.val.1 (N.source_mem f.val f.property) hef
  · exact hrate

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set
open scoped BigOperators

namespace Problem326.BarrierConstruction

/-- The uniform conclusion needed from the arbitrary-tolerance affine lemma.
Slopes are fixed before `h` is
chosen, and every minimizing branch, including ties, must approximate. -/
def UniformAffineApproximation (d : ℕ) : Prop :=
  ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
    ∃ n : ℕ, 0 < n ∧ ∃ (r : Fin n → Fin d → ℝ)
      (c : Fin n → ℝ → ℝ) (h₀ : ℝ), 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
        (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
          AffineActive r (fun k => c k h) (fun i => h ^ p i) j →
          ∀ i, |p i - r j i| < E (r j)

/-- Finite barrier data, after the network, rates, and initial point have been
fixed. The remaining analytic step is trapping and global ODE continuation. -/
structure AffineBarrierData {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x₀ : Fin d → ℝ) where
  n : ℕ
  n_pos : 0 < n
  slope : Fin n → Fin d → ℝ
  offset : Fin n → ℝ
  parameter : ℝ
  parameter_pos : 0 < parameter
  parameter_lt_one : parameter < 1
  constant_branch : Fin n
  slope_constant : slope constant_branch = 0
  initial_active : AffineActive slope offset x₀ constant_branch
  initial_inside : ∀ i, parameter < x₀ i ∧ x₀ i < parameter⁻¹
  inward : ∀ p : Fin d → ℝ, (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
    AffineActive slope offset (fun i => parameter ^ p i) j →
    0 ≤ dot (slope j) (massAction N κ (fun i => parameter ^ p i))
  boundary_excluded : ∀ p : Fin d → ℝ, (∀ i, |p i| ≤ 1) →
    (∃ i, |p i| = 1) →
    ¬ AffineActive slope offset (fun i => parameter ^ p i) constant_branch

/-- Coordinate directions are included alongside all complex differences. -/
def coordinateDirection {d : ℕ} (i : Fin d) : Fin d → ℝ :=
  fun k => if k = i then 1 else 0

def complexDifference {d : ℕ} (y z : Fin d → ℕ) : Fin d → ℝ :=
  fun i => (z i : ℝ) - (y i : ℝ)

@[simp] theorem dot_coordinateDirection {d : ℕ} (p : Fin d → ℝ) (i : Fin d) :
    dot p (coordinateDirection i) = p i := by
  classical
  simp [dot, coordinateDirection, mul_ite]

@[simp] theorem dot_complexDifference {d : ℕ} (p : Fin d → ℝ)
    (y z : Fin d → ℕ) :
    dot p (complexDifference y z) =
      dot p (fun i => (z i : ℝ)) - dot p (fun i => (y i : ℝ)) := by
  simp [dot, complexDifference, mul_sub, Finset.sum_sub_distrib]

def comparisonDirections {d : ℕ} (N : ReactionNetwork d) : Finset (Fin d → ℝ) :=
  (Finset.univ.image coordinateDirection) ∪
    ((N.complexes.product N.complexes).image
      (fun yz => complexDifference yz.1 yz.2))

theorem coordinateDirection_mem {d : ℕ} (N : ReactionNetwork d) (i : Fin d) :
    coordinateDirection i ∈ comparisonDirections N := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem complexDifference_mem {d : ℕ} (N : ReactionNetwork d)
    {y z : Fin d → ℕ} (hy : y ∈ N.complexes) (hz : z ∈ N.complexes) :
    complexDifference y z ∈ comparisonDirections N := by
  classical
  unfold comparisonDirections
  rw [Finset.mem_union]
  right
  apply Finset.mem_image.mpr
  exact ⟨(y, z), Finset.mem_product.mpr ⟨hy, hz⟩, rfl⟩

/-- The full network-aware algebraic assembly. The tolerance is selected first,
then fixed slopes and their positive gap, then the single small parameter.
No compactness or ODE conclusion is assumed in this theorem. -/
theorem exists_affineBarrierData {d : ℕ}
    (happroximation : UniformAffineApproximation d)
    (N : ReactionNetwork d) (κ : Reaction N → ℝ)
    (hweak : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x₀ : Fin d → ℝ) (hx₀ : PositiveState x₀) :
    Nonempty (AffineBarrierData N κ x₀) := by
  classical
  let D := comparisonDirections N
  obtain ⟨E, hE, hEcontrol⟩ := exists_sign_tolerance_function D
  obtain ⟨n, hn, r, c, h₀, hh₀, happ⟩ :=
    happroximation E (fun v => (hE v).1)
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨H, hH, hHone, hHgap⟩ :=
    exists_uniform_dot_gap (Finset.univ.image r) D
  obtain ⟨h, p₀, hh, hhsmall, hh1, hp₀, hrec, hrate⟩ :=
    exists_initial_exponent_parameter x₀ κ hx₀ hH hh₀ hκ
  let cs : Fin n → ℝ := fun j => c j h
  have hcontrol (p : Fin d → ℝ) (hp : ∀ i, |p i| ≤ 1)
      (j : Fin n) (ha : AffineActive r cs (fun i => h ^ p i) j)
      (v : Fin d → ℝ) (hv : v ∈ D) (hne : dot (r j) v ≠ 0) :
      (0 < dot p v ↔ 0 < dot (r j) v) ∧ H < |dot p v| := by
    have hc := hEcontrol (r j) p (happ h hh hhsmall p hp j ha) v hv hne
    have hg := hHgap (r j) (Finset.mem_image_of_mem r (Finset.mem_univ j)) v hv hne
    exact ⟨hc.1, lt_of_le_of_lt hg hc.2.2⟩
  have hp₀cube : ∀ i, |p₀ i| ≤ 1 := fun i => (hp₀ i).le.trans hHone
  have hpoint : (fun i => h ^ p₀ i) = x₀ := funext hrec
  have hinitialgap : ∀ j, AffineActive r cs x₀ j →
      ∀ i, r j i ≠ 0 → H ≤ |p₀ i| := by
    intro j hj i hne
    have ha : AffineActive r cs (fun i => h ^ p₀ i) j := by rwa [hpoint]
    have hc := hcontrol p₀ hp₀cube j ha (coordinateDirection i)
      (coordinateDirection_mem N i) (by simpa using hne)
    simpa using hc.2.le
  obtain ⟨j₀, hj₀⟩ := exists_affineActive r cs x₀
  have hzero : r j₀ = 0 := affineActive_slope_eq_zero r cs x₀ p₀ hp₀ hinitialgap hj₀
  refine ⟨{
    n := n
    n_pos := hn
    slope := r
    offset := cs
    parameter := h
    parameter_pos := hh
    parameter_lt_one := hh1
    constant_branch := j₀
    slope_constant := hzero
    initial_active := hj₀
    initial_inside := ?_
    inward := ?_
    boundary_excluded := ?_ }⟩
  · intro i
    obtain ⟨hpneg, hppos⟩ := abs_lt.mp ((hp₀ i).trans_le hHone)
    constructor
    · have ht := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hppos
      simpa only [Real.rpow_one, hrec i] using ht
    · have ht := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hpneg
      simpa only [Real.rpow_neg_one, hrec i] using ht
  · intro p hp j ha
    apply massAction_inward_of_monomial_order N κ (fun i => h ^ p i) (r j) (h ^ H)
      hweak (fun i => Real.rpow_pos_of_pos hh _) hκ (Real.rpow_nonneg hh.le _) ?_ hrate
    intro y hy z hz hyz
    have hrv : 0 < dot (r j) (complexDifference y z) := by
      rw [dot_complexDifference]
      exact sub_pos.mpr hyz
    have hc := hcontrol p hp j ha (complexDifference y z)
      (complexDifference_mem N hy hz) (ne_of_gt hrv)
    have hpv : 0 < dot p (complexDifference y z) := hc.1.mpr hrv
    have hg : H ≤ dot p (complexDifference y z) := by
      simpa only [abs_of_pos hpv] using hc.2.le
    exact monomial_le_rpow_mul_of_gap hh hh1.le p y z hg
  · intro p hp hpboundary
    exact constant_branch_not_active_on_boundary r cs (fun p i => h ^ p i) E
      (hE 0).2 hzero hpboundary (fun ha => happ h hh hhsmall p hp j₀ ha)

end Problem326.BarrierConstruction

end

end OAI
end
end

section
section
namespace OAI


/-! Geometry of the reciprocal box used by the affine certificate. -/

namespace Problem326

open Set

/-- The interior of a finite coordinate box is obtained by making every
coordinate inequality strict. -/
theorem mem_interior_coordinate_box_iff
    {ι : Type uIota} [Finite ι] {a b x : ι → ℝ} :
    x ∈ interior (Icc a b) ↔ ∀ i, a i < x i ∧ x i < b i := by
  rw [← pi_univ_Icc, interior_pi_set (Set.toFinite Set.univ)]
  simp only [interior_Icc, mem_pi, mem_univ, mem_Ioo, forall_true_left]

/-- A positive state has every logarithmic exponent strictly between -1
and 1 exactly when it belongs to the interior of the reciprocal box. -/
theorem mem_interior_reciprocal_box_iff
    {ι : Type uIota} [Finite ι] {x : ι → ℝ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hx : ∀ i, 0 < x i) :
    x ∈ interior (Icc (fun _ => h) (fun _ => h⁻¹)) ↔
      ∀ i, |Real.log (x i) / Real.log h| < 1 := by
  rw [mem_interior_coordinate_box_iff]
  exact forall_congr' fun i => (abs_log_coordinate_lt_one_iff hh hh1 (hx i)).symm

/-- Closed reciprocal boxes in finitely many real coordinates are compact. -/
theorem isCompact_reciprocal_box {ι : Type uIota} [Finite ι] (h : ℝ) :
    IsCompact (Icc (fun _ : ι => h) (fun _ => h⁻¹)) := by
  rw [← pi_univ_Icc]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- Every point in a positive reciprocal box is positive, and its unique
logarithmic exponents lie in the closed unit cube. -/
theorem reciprocal_box_log_coordinates
    {ι : Type uIota} {x : ι → ℝ} {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hx : x ∈ Icc (fun _ => h) (fun _ => h⁻¹)) :
    (∀ i, 0 < x i) ∧
      (∀ i, |Real.log (x i) / Real.log h| ≤ 1) ∧
      (∀ i, h ^ (Real.log (x i) / Real.log h) = x i) := by
  have hpositive : ∀ i, 0 < x i := fun i => hh.trans_le (hx.1 i)
  exact ⟨hpositive,
    fun i => (abs_log_coordinate_le_one_iff hh hh1 (hpositive i)).mpr
      ⟨hx.1 i, hx.2 i⟩,
    fun i => rpow_log_coordinate hh hh1 (hpositive i)⟩

/-- A boundary point of the reciprocal box has a logarithmic coordinate
of absolute value one.  This is the boundary obstruction used to exclude
an active zero-slope label. -/
theorem reciprocal_box_frontier_coordinate
    {ι : Type uIota} [Finite ι] {x : ι → ℝ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1)
    (hx : x ∈ frontier (Icc (fun _ => h) (fun _ => h⁻¹))) :
    ∃ i, |Real.log (x i) / Real.log h| = 1 := by
  have hxbox : x ∈ Icc (fun _ => h) (fun _ => h⁻¹) :=
    isClosed_Icc.frontier_subset hx
  obtain ⟨hpositive, hunit, -⟩ := reciprocal_box_log_coordinates hh hh1 hxbox
  have hnot : ¬ ∀ i, |Real.log (x i) / Real.log h| < 1 := by
    intro hall
    exact hx.2 ((mem_interior_reciprocal_box_iff hh hh1 hpositive).mpr hall)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  exact ⟨i, le_antisymm (hunit i) hi⟩

end Problem326

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set

namespace Problem326.BarrierConstruction.AffineBarrierData

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {x₀ : Fin d → ℝ}

/-- The physical reciprocal box for a constructed affine barrier. -/
def box (A : AffineBarrierData N κ x₀) : Set (Fin d → ℝ) :=
  Icc (fun _ => A.parameter) (fun _ => A.parameter⁻¹)

/-- The plateau selected by the constant branch, as finite affine inequalities. -/
def plateau (A : AffineBarrierData N κ x₀) : Set (Fin d → ℝ) :=
  {x | ∀ j, A.offset A.constant_branch ≤ dot (A.slope j) x + A.offset j}

theorem mem_plateau_iff_active (A : AffineBarrierData N κ x₀) (x : Fin d → ℝ) :
    x ∈ A.plateau ↔ AffineActive A.slope A.offset x A.constant_branch := by
  simp only [plateau, Set.mem_ofPred_eq, AffineActive, A.slope_constant, dot,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem initial_mem_plateau (A : AffineBarrierData N κ x₀) : x₀ ∈ A.plateau :=
  (A.mem_plateau_iff_active x₀).mpr A.initial_active

theorem initial_mem_interior_box (A : AffineBarrierData N κ x₀) :
    x₀ ∈ interior A.box :=
  mem_interior_coordinate_box_iff.mpr A.initial_inside

theorem isCompact_box (A : AffineBarrierData N κ x₀) : IsCompact A.box :=
  isCompact_reciprocal_box A.parameter

theorem isClosed_box (A : AffineBarrierData N κ x₀) : IsClosed A.box := isClosed_Icc

theorem box_subset_positive (A : AffineBarrierData N κ x₀) :
    A.box ⊆ {x | PositiveState x} := by
  intro x hx i
  exact A.parameter_pos.trans_le (hx.1 i)

/-- Transfer the inward estimate from exponential coordinates to every physical
point of the box. Strict positivity follows from box membership, not from an
unproved positivity theorem for trajectories. -/
theorem inward_on_box (A : AffineBarrierData N κ x₀)
    {x : Fin d → ℝ} (hx : x ∈ A.box) {j : Fin A.n}
    (hj : AffineActive A.slope A.offset x j) :
    0 ≤ dot (A.slope j) (massAction N κ x) := by
  obtain ⟨hpositive, hunit, hrec⟩ :=
    reciprocal_box_log_coordinates A.parameter_pos A.parameter_lt_one hx
  have heq : (fun i => A.parameter ^ (Real.log (x i) / Real.log A.parameter)) = x :=
    funext hrec
  have ha : AffineActive A.slope A.offset
      (fun i => A.parameter ^ (Real.log (x i) / Real.log A.parameter)) j := by
    simpa only [heq] using hj
  have hi := A.inward (fun i => Real.log (x i) / Real.log A.parameter) hunit j ha
  simpa only [heq] using hi

/-- A frontier point has an exponent coordinate of absolute value one, where
the constant branch cannot be active. -/
theorem constant_not_active_on_frontier (A : AffineBarrierData N κ x₀)
    {x : Fin d → ℝ} (hx : x ∈ frontier A.box) :
    ¬ AffineActive A.slope A.offset x A.constant_branch := by
  have hxbox := A.isClosed_box.frontier_subset hx
  obtain ⟨hpositive, hunit, hrec⟩ :=
    reciprocal_box_log_coordinates A.parameter_pos A.parameter_lt_one hxbox
  have heq : (fun i => A.parameter ^ (Real.log (x i) / Real.log A.parameter)) = x :=
    funext hrec
  have hboundary := reciprocal_box_frontier_coordinate
    A.parameter_pos A.parameter_lt_one hx
  have ha := A.boundary_excluded
    (fun i => Real.log (x i) / Real.log A.parameter) hunit hboundary
  simpa only [heq] using ha

theorem plateau_disjoint_frontier (A : AffineBarrierData N κ x₀) :
    Disjoint A.plateau (frontier A.box) := by
  apply Set.disjoint_left.mpr
  intro x hx hxb
  exact A.constant_not_active_on_frontier hxb ((A.mem_plateau_iff_active x).mp hx)

theorem plateau_isFinitePolyhedron (A : AffineBarrierData N κ x₀) :
    IsFinitePolyhedron A.plateau :=
  finiteAffine_superlevel_isFinitePolyhedron A.slope A.offset (A.offset A.constant_branch)

theorem plateau_subset_interior_box (A : AffineBarrierData N κ x₀) :
    A.plateau ⊆ interior A.box :=
  Geometry.subset_interior_of_disjoint_frontier A.plateau_isFinitePolyhedron.convex.isPreconnected
    ⟨x₀, A.initial_mem_plateau, A.initial_mem_interior_box⟩ A.plateau_disjoint_frontier

theorem isCompact_plateau (A : AffineBarrierData N κ x₀) : IsCompact A.plateau :=
  A.isCompact_box.of_isClosed_subset A.plateau_isFinitePolyhedron.isClosed
    (A.plateau_subset_interior_box.trans interior_subset)

theorem plateau_subset_positive (A : AffineBarrierData N κ x₀) :
    A.plateau ⊆ {x | PositiveState x} :=
  A.plateau_subset_interior_box.trans (interior_subset.trans A.box_subset_positive)

/-- The plateau is a compact convex polyhedron containing the initial point
and lying strictly in the positive orthant. -/
theorem geometric_properties (A : AffineBarrierData N κ x₀) :
    IsCompact A.plateau ∧ Convex ℝ A.plateau ∧ IsFinitePolyhedron A.plateau ∧
      x₀ ∈ A.plateau ∧ A.plateau ⊆ {x | PositiveState x} :=
  ⟨A.isCompact_plateau, A.plateau_isFinitePolyhedron.convex, A.plateau_isFinitePolyhedron,
    A.initial_mem_plateau, A.plateau_subset_positive⟩

end Problem326.BarrierConstruction.AffineBarrierData

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326

/-- Pairing the mass-action vector field with a fixed normal commutes with
its finite reaction sum. This is the algebraic bridge to ordered-cut flux. -/
theorem dot_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x r : Fin d → ℝ) :
    dot r (massAction N κ x) =
      ∑ e : Reaction N, κ e * monomial x e.val.1 *
        (dot r (fun i => (e.val.2 i : ℝ)) -
          dot r (fun i => (e.val.1 i : ℝ))) := by
  classical
  unfold dot massAction
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The derivative of a fixed linear functional along a differentiable curve. -/
theorem hasDerivAt_dot {d : ℕ} {x : ℝ → (Fin d → ℝ)}
    {v : Fin d → ℝ} {t : ℝ} (hx : HasDerivAt x v t)
    (r : Fin d → ℝ) :
    HasDerivAt (fun s => dot r (x s)) (dot r v) t := by
  unfold dot
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_pi.mp hx i).const_mul (r i)

/-- Affine labels have the expected derivative along solution curves. -/
theorem hasDerivAt_affineLabel {d : ℕ} {x : ℝ → (Fin d → ℝ)}
    {v : Fin d → ℝ} {t : ℝ} (hx : HasDerivAt x v t)
    (r : Fin d → ℝ) (c : ℝ) :
    HasDerivAt (fun s => dot r (x s) + c) (dot r v) t := by
  simpa using (hasDerivAt_dot hx r).add_const c

/-- The derivative of an affine label along a local mass-action solution,
expressed in the scalar form used by the finite graph estimate. -/
theorem IsForwardSolutionOn.hasDerivAt_affineLabel {d : ℕ}
    {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {x0 : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardSolutionOn N κ x0 T x) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (r : Fin d → ℝ) (c : ℝ) :
    HasDerivAt (fun s => dot r (x s) + c)
      (∑ e : Reaction N, κ e * monomial (x t) e.val.1 *
        (dot r (fun i => (e.val.2 i : ℝ)) -
          dot r (fun i => (e.val.1 i : ℝ)))) t := by
  rw [← dot_massAction]
  exact Problem326.hasDerivAt_affineLabel (hx.2.2 t ht) r c

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326.Barrier

/-- The finite affine minimum used as a barrier. All minimizing labels are
active; no tie-breaking convention is built into this definition. -/
def affineMinimum {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → Fin d → ℝ) (c : ι → ℝ) (z : Fin d → ℝ) : ℝ :=
  s.inf' hs (fun i => dot (a i) z + c i)

/-- Finite-segment trapping for a vector field with nonnegative derivatives
of every active affine branch. This theorem does not assume a global solution
or any reaction-network property: those enter only when supplying `hactive`. -/
theorem affine_minimum_traps_segment
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → Fin d → ℝ) (c : ι → ℝ)
    {B : Set (Fin d → ℝ)} {M T : ℝ}
    {f : (Fin d → ℝ) → (Fin d → ℝ)} {x : ℝ → (Fin d → ℝ)}
    (hT : 0 ≤ T) (hB : IsClosed B)
    (hceil : ∀ z, affineMinimum s hs a c z ≤ M)
    (hboundary : ∀ z ∈ frontier B, affineMinimum s hs a c z ≠ M)
    (hactive : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = affineMinimum s hs a c z →
      0 ≤ dot (a i) (f z))
    (hx : ContinuousOn x (Set.Icc 0 T))
    (hxderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hx0 : x 0 ∈ interior B)
    (hF0 : affineMinimum s hs a c (x 0) = M) :
    Set.MapsTo x (Set.Icc 0 T)
      {z | z ∈ interior B ∧ affineMinimum s hs a c z = M} := by
  apply Geometry.mapsTo_plateau_of_monotone_on_box hT hB hx hx0 hceil hF0 hboundary
  intro τ hτ hseg
  change MonotoneOn
    (fun t => s.inf' hs (fun i => dot (a i) (x t) + c i)) (Set.Icc 0 τ)
  apply monotoneOn_finset_inf'_of_active_deriv_nonneg hs
  · intro i hi
    have hc : Continuous (fun z : Fin d → ℝ => dot (a i) z + c i) := by
      unfold dot
      fun_prop
    exact hc.comp_continuousOn (hx.mono (Set.Icc_subset_Icc le_rfl hτ.2))
  · intro t ht i hi hai
    refine ⟨dot (a i) (f (x t)), ?_, ?_⟩
    · exact hactive (x t) (hseg ⟨ht.1.le, ht.2.le⟩) i hi hai
    · exact hasDerivAt_affineLabel
        (hxderiv t ⟨ht.1, ht.2.trans_le hτ.2⟩) (a i) (c i)

theorem forward_solution_trapped
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → Fin d → ℝ) (c : ι → ℝ)
    {B : Set (Fin d → ℝ)} {M T : ℝ} {x0 : Fin d → ℝ}
    {x : ℝ → (Fin d → ℝ)} (hT : 0 ≤ T) (hB : IsClosed B)
    (hceil : ∀ z, affineMinimum s hs a c z ≤ M)
    (hboundary : ∀ z ∈ frontier B, affineMinimum s hs a c z ≠ M)
    (hactive : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = affineMinimum s hs a c z →
      0 ≤ dot (a i) (massAction N κ z))
    (hx : IsForwardSolutionOn N κ x0 T x)
    (hx0 : x0 ∈ interior B) (hF0 : affineMinimum s hs a c x0 = M) :
    Set.MapsTo x (Set.Icc 0 T)
      {z | z ∈ interior B ∧ affineMinimum s hs a c z = M} := by
  exact affine_minimum_traps_segment s hs a c hT hB hceil hboundary hactive
    hx.2.1 hx.2.2 (hx.1.symm ▸ hx0) (hx.1.symm ▸ hF0)

end Problem326.Barrier

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Metric

namespace Problem326

/-- A continuously differentiable autonomous vector field admits a solution on a
closed interval of positive length, with ordinary derivatives at both endpoints. -/
theorem exists_local_solution_of_contDiffAt
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {z : E} (hf : ContDiffAt ℝ 1 f z) (t₀ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∃ x : ℝ → E, x t₀ = z ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivAt x (f (x t)) t := by
  obtain ⟨x, hx, ε, hε, hderiv⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  refine ⟨ε / 2, half_pos hε, x, hx, ?_⟩
  intro t ht
  apply hderiv t
  constructor <;> linarith [ht.1, ht.2]

/-- The local existence time can be chosen uniformly over a compact set of
initial states. This supplies fixed-size steps for compact trapping arguments. -/
theorem exists_uniform_local_solution_on_compact
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K)
    (t₀ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∃ x : ℝ → E, x t₀ = z ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivAt x (f (x t)) t := by
  classical
  have hlocal := fun z : E =>
    (hf.contDiffAt (x := z)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt t₀
  choose r hr ε hε hsol using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun z => ball z (r z))
    (fun _ => isOpen_ball) (fun z _ => mem_iUnion.mpr ⟨z, mem_ball_self (hr z)⟩)
  let s' := insert (0 : E) s
  have hs' : s'.Nonempty := Finset.insert_nonempty _ _
  let T : ℝ := s'.inf' hs' (fun z => ε z / 2)
  have hT : 0 < T := by
    dsimp [T]
    exact (Finset.lt_inf'_iff hs').mpr (fun z _ => half_pos (hε z))
  refine ⟨T, hT, ?_⟩
  intro z hz
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
  obtain ⟨x, hx, hderiv⟩ := hsol w z (ball_subset_closedBall hzw)
  have hTw : T ≤ ε w / 2 := Finset.inf'_le _ (Finset.mem_insert_of_mem hw)
  refine ⟨x, hx, ?_⟩
  intro t ht
  apply hderiv t
  constructor <;> linarith [ht.1, ht.2, hε w]

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Filter
open scoped Topology

namespace Problem326

/-- Two differentiable curves with the same value and derivative at a joining
time can be glued there without losing differentiability. -/
theorem hasDerivAt_join
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : ℝ → E} {c : ℝ} {v : E}
    (hx : HasDerivAt x v c) (hy : HasDerivAt y v c) (hxy : x c = y c) :
    HasDerivAt (fun t => if t ≤ c then x t else y t) v c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then x t else y t) v (Iic c) c :=
    hx.hasDerivWithinAt.congr (fun t ht => ite_eq_left ht) (ite_eq_left le_rfl)
  have hr : HasDerivWithinAt (fun t => if t ≤ c then x t else y t) v (Ioi c) c :=
    hy.hasDerivWithinAt.congr (fun t ht => ite_eq_right (not_le.mpr ht))
      (by simpa using hxy)
  have h := hl.union hr
  simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using h

/-- Concatenation of autonomous ODE solutions. Ordinary derivatives at the end
points avoid a separate endpoint extension argument. -/
theorem hasDerivAt_join_on_Icc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x y : ℝ → E} {a c b : ℝ}
    (hx : ∀ t ∈ Icc a c, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Icc c b, HasDerivAt y (f (y t)) t)
    (hxy : x c = y c) :
    ∀ t ∈ Icc a b,
      HasDerivAt (fun s => if s ≤ c then x s else y s)
        (f (if t ≤ c then x t else y t)) t := by
  intro t ht
  rcases lt_trichotomy t c with htc | heq | hct
  · have heq : (fun s => if s ≤ c then x s else y s) =ᶠ[𝓝 t] x := by
      filter_upwards [eventually_lt_nhds htc] with s hs
      exact ite_eq_left hs.le
    simpa only [ite_eq_left htc.le] using
      (hx t ⟨ht.1, htc.le⟩).congr_of_eventuallyEq heq
  · subst t
    have hxc := hx c ⟨ht.1, le_rfl⟩
    have hyc : HasDerivAt y (f (x c)) c := by
      simpa only [hxy] using hy c ⟨le_rfl, ht.2⟩
    simpa only [ite_eq_left le_rfl] using hasDerivAt_join hxc hyc hxy
  · have heq : (fun s => if s ≤ c then x s else y s) =ᶠ[𝓝 t] y := by
      filter_upwards [eventually_gt_nhds hct] with s hs
      exact ite_eq_right (not_le.mpr hs)
    simpa only [ite_eq_right (not_le.mpr hct)] using
      (hy t ⟨hct.le, ht.2⟩).congr_of_eventuallyEq heq

/-- A uniform local existence statement extends a finite solution by one fixed
step whenever its endpoint remains in the allowed set. -/
theorem exists_extend_solution_on_Icc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {K : Set E} {T a c : ℝ} {x : ℝ → E}
    (hlocal : ∀ z ∈ K, ∃ y : ℝ → E, y 0 = z ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (f (y t)) t)
    (hx : ∀ t ∈ Icc a c, HasDerivAt x (f (x t)) t)
    (hxc : x c ∈ K) :
    ∃ x' : ℝ → E, EqOn x' x (Iic c) ∧
      ∀ t ∈ Icc a (c + T), HasDerivAt x' (f (x' t)) t := by
  obtain ⟨y, hy0, hy⟩ := hlocal (x c) hxc
  let ys : ℝ → E := fun t => y (t - c)
  have hys : ∀ t ∈ Icc c (c + T), HasDerivAt ys (f (ys t)) t := by
    intro t ht
    have htd : t - c ∈ Icc (0 : ℝ) T := by
      constructor <;> linarith [ht.1, ht.2]
    simpa [ys, Function.comp_def] using (hy (t - c) htd).scomp t ((hasDerivAt_id t).sub_const c)
  have hxy : x c = ys c := by simp [ys, hy0]
  refine ⟨fun t => if t ≤ c then x t else ys t, ?_, ?_⟩
  · exact fun t ht => ite_eq_left ht
  · exact hasDerivAt_join_on_Icc hx hys hxy

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Set Filter
open scoped Topology

namespace Problem326

/-- A compatible sequence of curves on intervals with unbounded right endpoints
has a global extension. Agreement on left half-lines preserves the germ at zero. -/
theorem exists_global_of_compatible_curves
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {a : ℝ} (b : ℕ → ℝ) (hb : Monotone b)
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < b n)
    (x : ℕ → ℝ → E)
    (hcompat : ∀ n, EqOn (x (n + 1)) (x n) (Iic (b n)))
    (hderiv : ∀ n, ∀ t ∈ Icc a (b n), HasDerivAt (x n) (f (x n t)) t) :
    ∃ g : ℝ → E, (∀ n, EqOn g (x n) (Iic (b n))) ∧
      ∀ t, a ≤ t → HasDerivAt g (f (g t)) t := by
  classical
  have hcompat' : ∀ n m, n ≤ m → EqOn (x m) (x n) (Iic (b n)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m hnm ih =>
      intro t ht
      exact (hcompat m (le_trans ht (hb hnm))).trans (ih ht)
  choose index hindex using hunbounded
  let g : ℝ → E := fun t => x (index t) t
  have heq : ∀ n, EqOn g (x n) (Iic (b n)) := by
    intro n t ht
    rcases le_total n (index t) with hle | hle
    · exact hcompat' n (index t) hle ht
    · exact (hcompat' (index t) n hle (hindex t).le).symm
  refine ⟨g, heq, ?_⟩
  intro t ht
  let n := index t
  have hn : t < b n := hindex t
  have hevent : g =ᶠ[𝓝 t] x n := by
    filter_upwards [eventually_lt_nhds hn] with s hs
    exact heq n hs.le
  rw [heq n hn.le]
  exact (hderiv n t ⟨ht, hn.le⟩).congr_of_eventuallyEq hevent

/-- Compact trapping turns local existence into a global forward solution.
Only trapping of finite, closed-interval solutions is assumed. -/
theorem exists_global_solution_of_compact_trapping
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ S : ℝ, 0 ≤ S → ∀ x : ℝ → E,
      x 0 = z →
      (∀ t ∈ Icc (0 : ℝ) S, HasDerivAt x (f (x t)) t) →
      ∀ t ∈ Icc (0 : ℝ) S, x t ∈ K)
    {z : E} (hz : z ∈ K) :
    ∃ g : ℝ → E, g 0 = z ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt g (f (g t)) t) ∧
      ∀ t : ℝ, 0 ≤ t → g t ∈ K := by
  classical
  obtain ⟨T, hT, hlocal⟩ := exists_uniform_local_solution_on_compact hf hK 0
  have hlocal' : ∀ z ∈ K, ∃ x : ℝ → E, x 0 = z ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt x (f (x t)) t := by
    simpa only [zero_sub, zero_add] using hlocal
  have hlocalForward : ∀ z ∈ K, ∃ x : ℝ → E, x 0 = z ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x (f (x t)) t := by
    intro q hq
    obtain ⟨x, hx, hd⟩ := hlocal' q hq
    exact ⟨x, hx, fun t ht => hd t ⟨by linarith [ht.1], ht.2⟩⟩
  let b : ℕ → ℝ := fun n => ((n : ℝ) + 1) * T
  have hb0 : ∀ n, 0 < b n := by
    intro n
    dsimp [b]
    positivity
  have hbsucc : ∀ n, b (n + 1) = b n + T := by
    intro n
    simp [b, Nat.cast_add, Nat.cast_one]
    ring
  let P : ℕ → (ℝ → E) → Prop := fun n x => x 0 = z ∧
    ∀ t ∈ Icc (-T) (b n), HasDerivAt x (f (x t)) t
  have hstart : ∃ x, P 0 x := by
    simpa [P, b] using hlocal' z hz
  have hstep : ∀ n x, P n x → ∃ y, P (n + 1) y ∧ EqOn y x (Iic (b n)) := by
    intro n x hx
    have hmem : x (b n) ∈ K := by
      apply htrap z hz (b n) (hb0 n).le x hx.1
      · exact fun t ht => hx.2 t ⟨by linarith [ht.1], ht.2⟩
      · exact ⟨(hb0 n).le, le_rfl⟩
    obtain ⟨y, heq, hdy⟩ := exists_extend_solution_on_Icc hlocalForward hx.2 hmem
    refine ⟨y, ⟨?_, ?_⟩, heq⟩
    · exact (heq (hb0 n).le).trans hx.1
    · simpa only [hbsucc n] using hdy
  let start : {x // P 0 x} := ⟨Classical.choose hstart, Classical.choose_spec hstart⟩
  let step : ∀ n, {x // P n x} → {x // P (n + 1) x} := fun n x =>
    ⟨Classical.choose (hstep n x.1 x.2), (Classical.choose_spec (hstep n x.1 x.2)).1⟩
  let curves : ∀ n, {x // P n x} := Nat.rec start step
  let x : ℕ → ℝ → E := fun n => (curves n).1
  have hx : ∀ n, P n (x n) := fun n => (curves n).2
  have hcompat : ∀ n, EqOn (x (n + 1)) (x n) (Iic (b n)) := by
    intro n
    exact (Classical.choose_spec (hstep n (curves n).1 (curves n).2)).2
  have hb : Monotone b := by
    intro n m hnm
    dsimp [b]
    apply mul_le_mul_of_nonneg_right _ hT.le
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < b n := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt (t / T)
    refine ⟨n, ?_⟩
    have ht : t < (n : ℝ) * T := (div_lt_iff₀ hT).mp hn
    dsimp [b]
    nlinarith
  obtain ⟨g, heq, hd⟩ := exists_global_of_compatible_curves b hb hunbounded x hcompat
    (fun n => (hx n).2)
  refine ⟨g, (heq 0 (hb0 0).le).trans (hx 0).1, ?_, ?_⟩
  · intro t ht
    exact hd t (by linarith)
  · intro t ht
    exact htrap z hz t ht g ((heq 0 (hb0 0).le).trans (hx 0).1)
      (fun s hs => hd s (by linarith [hs.1])) t ⟨ht, le_rfl⟩

end Problem326

end

end OAI
end
end

section
section
namespace OAI


open Set Filter
open scoped Topology

namespace Problem326

section AutonomousODE
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : E → E} {f g : ℝ → E} {a b : ℝ}

/-- The ODE and continuity extend the derivative to the initial endpoint. -/
theorem hasDerivWithinAt_initial_of_ode
    (hv : Continuous v) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t) :
    HasDerivWithinAt f (v (f a)) (Ici a) a := by
  have hc : ContinuousWithinAt f (Ioo a b) a :=
    (hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hc' : ContinuousWithinAt f (Ioi a) a :=
    hc.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hab)
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hf' t ht).differentiableAt.differentiableWithinAt)
    hc (Ioo_mem_nhdsGT hab)
  have heq : (fun t => v (f t)) =ᶠ[𝓝[>] a] deriv f := by
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (hf' t ht).deriv.symm
  exact Filter.Tendsto.congr' heq (hv.continuousAt.tendsto.comp hc')

/-- Uniqueness on a closed interval only requires the ODE on its interior. -/
theorem eqOn_Icc_of_locallyLipschitz_ode
    (hv : LocallyLipschitz v) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v (g t)) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simpa only [Icc_self, eqOn_singleton] using ha
  let S := (f '' Icc a b) ∪ (g '' Icc a b)
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨K, hK⟩ := hv.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  have hfa := hasDerivWithinAt_initial_of_ode hv.continuous hab hf hf'
  have hga := hasDerivWithinAt_initial_of_ode hv.continuous hab hg hg'
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => v) (s := fun _ => S)
    (K := K) (fun _ _ => hK) hf ?_ ?_ hg ?_ ?_ ha
  · intro t ht
    by_cases hta : t = a
    · simpa only [hta] using hfa
    · exact (hf' t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩).hasDerivWithinAt
  · intro t ht
    exact Or.inl (mem_image_of_mem f ⟨ht.1, ht.2.le⟩)
  · intro t ht
    by_cases hta : t = a
    · simpa only [hta] using hga
    · exact (hg' t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩).hasDerivWithinAt
  · intro t ht
    exact Or.inr (mem_image_of_mem g ⟨ht.1, ht.2.le⟩)

end AutonomousODE
end Problem326

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem326

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {z : Fin d → ℝ} {T : ℝ} {x y : ℝ → (Fin d → ℝ)}

/-- Uniqueness for finite forward solutions, including both endpoints. -/
theorem IsForwardSolutionOn.eqOn
    (hv : LocallyLipschitz (massAction N κ)) (hT : 0 ≤ T)
    (hx : IsForwardSolutionOn N κ z T x)
    (hy : IsForwardSolutionOn N κ z T y) :
    Set.EqOn x y (Set.Icc (0 : ℝ) T) :=
  eqOn_Icc_of_locallyLipschitz_ode hv hT hx.2.1 hx.2.2 hy.2.1 hy.2.2
    (hx.1.trans hy.1.symm)

/-- One invariant global trajectory from each initial point suffices for the
full finite-segment and extension definition of forward invariance. -/
theorem isForwardInvariant_of_global_trajectories
    (hv : LocallyLipschitz (massAction N κ)) {K : Set (Fin d → ℝ)}
    (hK : ∀ z ∈ K, ∃ x : ℝ → (Fin d → ℝ),
      IsGlobalForwardSolution N κ z x ∧ ∀ t : ℝ, 0 ≤ t → x t ∈ K) :
    IsForwardInvariant N κ K := by
  intro z hz
  obtain ⟨xg, hxg, hmem⟩ := hK z hz
  refine ⟨⟨xg, hxg⟩, ?_⟩
  intro T x hT hx
  have hg : IsForwardSolutionOn N κ z T xg := by
    refine ⟨hxg.1, ?_, ?_⟩
    · intro t ht
      exact (hxg.2 t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      exact hxg.2 t ht.1.le
  have heq : Set.EqOn xg x (Set.Icc (0 : ℝ) T) := hg.eqOn hv hT hx
  refine ⟨?_, ⟨xg, hxg, heq⟩⟩
  intro t ht
  rw [← heq ht]
  exact hmem t ht.1

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set

namespace Problem326

theorem exists_global_massAction_of_compact_trapping
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    (hreg : ContDiff ℝ 1 (massAction N κ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)),
      0 ≤ T → IsForwardSolutionOn N κ z T x →
      ∀ t ∈ Icc (0 : ℝ) T, x t ∈ K)
    {z : Fin d → ℝ} (hz : z ∈ K) :
    ∃ g : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ z g ∧
      ∀ t : ℝ, 0 ≤ t → g t ∈ K := by
  obtain ⟨g, hg0, hgd, hgK⟩ := exists_global_solution_of_compact_trapping hreg hK
    (fun q hq T hT x hx hd => htrap q hq T x hT
      ⟨hx, fun t ht => (hd t ht).continuousAt.continuousWithinAt,
        fun t ht => hd t (Ioo_subset_Icc_self ht)⟩) hz
  exact ⟨g, ⟨hg0, hgd⟩, hgK⟩

theorem isForwardInvariant_of_compact_trapping
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    (hreg : ContDiff ℝ 1 (massAction N κ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)),
      0 ≤ T → IsForwardSolutionOn N κ z T x →
      ∀ t ∈ Icc (0 : ℝ) T, x t ∈ K) :
    IsForwardInvariant N κ K := by
  apply isForwardInvariant_of_global_trajectories hreg.locallyLipschitz
  intro z hz
  exact exists_global_massAction_of_compact_trapping hreg hK htrap hz

/-- No extra regularity hypothesis is necessary for the polynomial mass-action
field: compact trapping of finite solutions implies full forward invariance. -/
theorem massAction_isForwardInvariant_of_compact_trapping
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)),
      0 ≤ T → IsForwardSolutionOn N κ z T x →
      ∀ t ∈ Icc (0 : ℝ) T, x t ∈ K) :
    IsForwardInvariant N κ K :=
  isForwardInvariant_of_compact_trapping (by
    unfold massAction monomial
    fun_prop) hK htrap

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set

namespace Problem326.BarrierConstruction

namespace AffineBarrierData

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {x₀ : Fin d → ℝ}

/-- The exact forward-invariance predicate follows from the constructed barrier,
with no separate global-solvability or regularity assumption. -/
theorem isForwardInvariant (A : AffineBarrierData N κ x₀) :
    Problem326.IsForwardInvariant N κ A.plateau := by
  classical
  let s : Finset (Fin A.n) := Finset.univ
  have hs : s.Nonempty := ⟨A.constant_branch, Finset.mem_univ _⟩
  let F := Barrier.affineMinimum s hs A.slope A.offset
  let M := A.offset A.constant_branch
  have hceil : ∀ x, F x ≤ M := by
    intro x
    dsimp only [F, M, Barrier.affineMinimum]
    have hi := Finset.inf'_le (fun j => dot (A.slope j) x + A.offset j)
      (show A.constant_branch ∈ s from Finset.mem_univ _)
    simpa only [A.slope_constant, dot, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add] using hi
  have hmem : ∀ x, x ∈ A.plateau ↔ F x = M := by
    intro x
    constructor
    · intro hx
      apply le_antisymm (hceil x)
      exact Finset.le_inf' hs _ (fun j _ => hx j)
    · intro hx j
      have hi := Finset.inf'_le (fun k => dot (A.slope k) x + A.offset k)
        (show j ∈ s from Finset.mem_univ _)
      change F x ≤ dot (A.slope j) x + A.offset j at hi
      simpa only [hx] using hi
  apply massAction_isForwardInvariant_of_compact_trapping A.isCompact_plateau
  intro z hz T x hT hx t ht
  have hboundary : ∀ y ∈ frontier A.box, F y ≠ M := by
    intro y hy hF
    exact A.constant_not_active_on_frontier hy
      ((A.mem_plateau_iff_active y).mp ((hmem y).mpr hF))
  have hactive : ∀ y ∈ A.box, ∀ j ∈ s,
      dot (A.slope j) y + A.offset j = F y →
      0 ≤ dot (A.slope j) (massAction N κ y) := by
    intro y hy j hj hjF
    apply A.inward_on_box hy
    intro k
    rw [hjF]
    exact Finset.inf'_le _ (show k ∈ s from Finset.mem_univ _)
  have htrap := Barrier.forward_solution_trapped s hs A.slope A.offset
    hT A.isClosed_box hceil hboundary hactive hx
    (A.plateau_subset_interior_box hz) ((hmem z).mp hz)
  exact (hmem (x t)).mpr (htrap ht).2

end AffineBarrierData

/-- Uniform arbitrary-tolerance affine approximation gives a compact convex
forward-invariant polytope with extension of every finite solution segment. -/
theorem compact_convex_invariant_polytope_of_uniform {d : ℕ}
    (happroximation : UniformAffineApproximation d)
    (N : ReactionNetwork d) (κ : Reaction N → ℝ)
    (hweak : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x₀ : Fin d → ℝ) (hx₀ : PositiveState x₀) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ Convex ℝ K ∧ IsFinitePolyhedron K ∧
      x₀ ∈ K ∧ K ⊆ {x | PositiveState x} ∧ IsForwardInvariant N κ K := by
  obtain ⟨A⟩ := exists_affineBarrierData happroximation N κ hweak hκ x₀ hx₀
  obtain ⟨hc, hv, hp, hx, hpos⟩ := A.geometric_properties
  exact ⟨A.plateau, hc, hv, hp, hx, hpos, A.isForwardInvariant⟩

end Problem326.BarrierConstruction

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326

/-- Coordinatewise projection onto a closed finite-dimensional box. -/
def coordinateClamp {ι : Type uIota} (a b : ι → ℝ) (hab : a ≤ b)
    (x : ι → ℝ) : ι → ℝ :=
  fun i => (Set.projIcc (a i) (b i) (hab i) (x i) : ℝ)

theorem coordinateClamp_mem {ι : Type uIota} (a b : ι → ℝ) (hab : a ≤ b)
    (x : ι → ℝ) : coordinateClamp a b hab x ∈ Set.Icc a b := by
  constructor
  · intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.1
  · intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.2

theorem coordinateClamp_eq_self {ι : Type uIota} {a b x : ι → ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) : coordinateClamp a b hab x = x := by
  funext i
  simp only [coordinateClamp, Set.projIcc_of_mem (hab i) ⟨hx.1 i, hx.2 i⟩]

theorem coordinateClamp_lipschitz {ι : Type uIota} [Fintype ι]
    (a b : ι → ℝ) (hab : a ≤ b) : LipschitzWith 1 (coordinateClamp a b hab) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  have hi : LipschitzWith 1
      (fun z : ℝ => (Set.projIcc (a i) (b i) (hab i) z : ℝ)) := by
    simpa only [one_mul, Function.comp_def] using
      (LipschitzWith.subtype_val (Set.Icc (a i) (b i))).comp
        (LipschitzWith.projIcc (hab i))
  calc
    dist (coordinateClamp a b hab x i) (coordinateClamp a b hab y i) ≤ dist (x i) (y i) := by
      simpa only [coordinateClamp, NNReal.coe_one, one_mul] using hi.dist_le_mul (x i) (y i)
    _ ≤ dist x y := dist_le_pi_dist x y i

/-- A continuously differentiable field has a globally bounded, globally
 Lipschitz extension of its restriction to any nonempty closed box.
 This permits global ODE existence to be separated from first-exit trapping. -/
theorem exists_bounded_lipschitz_extension {ι : Type uIota} {F : Type uF} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (ι → ℝ) → F} (hf : ContDiff ℝ 1 f)
    (a b : ι → ℝ) (hab : a ≤ b) :
    ∃ (g : (ι → ℝ) → F) (K : NNReal) (L : ℝ), 0 < L ∧
      LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ L) ∧ Set.EqOn g f (Set.Icc a b) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc a b) isCompact_Icc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuous.continuousOn
  refine ⟨f ∘ coordinateClamp a b hab, K, max C 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (coordinateClamp a b hab) Set.univ (Set.Icc a b) :=
      fun x _ => coordinateClamp_mem a b hab x
    simpa only [mul_one] using lipschitzOnWith_univ.mp
      (hK.comp (coordinateClamp_lipschitz a b hab).lipschitzOnWith hmaps)
  · intro x
    exact (hC _ (coordinateClamp_mem a b hab x)).trans (le_max_left _ _)
  · intro x hx
    simp only [Function.comp_apply, coordinateClamp_eq_self hab hx]

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326

/-- A compact set in a finite-dimensional positive orthant lies in a uniform
positive box. Neither nonemptiness nor positive dimension is necessary. -/
theorem compact_positive_uniform_bounds {ι : Type uIota} [Finite ι]
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∀ i, 0 < x i) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ x ∈ K, ∀ i, ε ≤ x i ∧ x i ≤ ε⁻¹ := by
  let S : Set ℝ := ⋃ i : ι, (fun x : ι → ℝ => x i) '' K
  have hS : IsCompact S :=
    isCompact_iUnion (fun i => hK.image (continuous_apply i))
  have hSpos : ∀ y ∈ S, 0 < y := by
    intro y hy
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
    exact hpos x hx i
  obtain ⟨a, ha, haS⟩ := hS.exists_forall_le' continuous_id.continuousOn hSpos
  have hinv : ContinuousOn (fun y : ℝ => y⁻¹) S :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (hSpos y hy))
  obtain ⟨b, hb, hbS⟩ := hS.exists_forall_le' hinv
    (fun y hy => inv_pos.mpr (hSpos y hy))
  let ε : ℝ := min (1 / 2) (min a b)
  have hε : 0 < ε := lt_min (by norm_num) (lt_min ha hb)
  refine ⟨ε, hε, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro x hx i
  have hmem : x i ∈ S := Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  have hεa : ε ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hεa.trans (haS _ hmem), ?_⟩
  have hle : ε ≤ (x i)⁻¹ := hεb.trans (hbS _ hmem)
  exact (le_inv_comm₀ hε (hpos x hx i)).mp hle

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326

/-- Every mass-action monomial is smooth on the whole ambient real space. -/
theorem contDiff_monomial {d : ℕ} (y : Fin d → ℕ) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ => monomial x y) := by
  unfold monomial
  fun_prop

/-- The mass-action vector field is polynomial, hence globally smooth. -/
theorem contDiff_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) : ContDiff ℝ ⊤ (massAction N κ) := by
  unfold massAction monomial
  fun_prop

theorem contDiff_one_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) : ContDiff ℝ 1 (massAction N κ) :=
  (contDiff_massAction N κ).of_le (by simp)

theorem locallyLipschitz_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) : LocallyLipschitz (massAction N κ) :=
  (contDiff_one_massAction N κ).locallyLipschitz

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326

/-- The quantitative global conclusion only needs a compact positive
forward-invariant set, not its polyhedral or convex structure. -/
theorem global_bounds_of_compact_invariant {d : ℕ}
    (N : ReactionNetwork d) (κ : Reaction N → ℝ) (x0 : Fin d → ℝ)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hx0 : x0 ∈ K)
    (hpos : K ⊆ {x | PositiveState x}) (hinv : IsForwardInvariant N κ K) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
      ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  obtain ⟨ε, hε, hεone, hbound⟩ := compact_positive_uniform_bounds hK
    (fun x hx => hpos hx)
  refine ⟨ε, hε, hεone, (hinv x0 hx0).1, ?_⟩
  intro x hx t ht i
  have hfinite : IsForwardSolutionOn N κ x0 t x := by
    refine ⟨hx.1, ?_, ?_⟩
    · intro s hs
      exact (hx.2 s hs.1).continuousAt.continuousWithinAt
    · intro s hs
      exact hx.2 s hs.1.le
  have hmem := ((hinv x0 hx0).2 t x ht hfinite).1 t ⟨ht, le_rfl⟩
  exact hbound (x t) hmem i

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326.Affine

/-- The lower-dimensional full certificates construct the canonical local
certificate in dimension `d`, with no additional existence hypothesis. -/
theorem localCertificate_of_lower_fullCertificates
    (d : ℕ) (hd : 0 < d)
    (ih : ∀ k : ℕ, k < d → ∀ a b : ℝ, ∀ E : (Fin k → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate k a b E))
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (_hab : a < b) (hE : ∀ r, Cube a b r → 0 < E r)
    (t : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    Nonempty (LocalCertificate d a b t E) := by
  have hE₀ : 0 < E (fun _ => t) := hE _ (fun _ => ⟨hat, htb⟩)
  by_cases htb' : t = b
  · subst t
    exact ⟨localCertificate_upper hd a b E hE₀⟩
  · have htb'' : t < b := lt_of_le_of_ne htb htb'
    apply localCertificate_of_layers hd htb'' E hE₀
    intro k hk hkd β htβ hβb
    obtain ⟨F, _, hF⟩ := exists_typeFamily_layerCertificate hk hkd htβ hβb E
      (fun r hr => hE r (fun i => ⟨hat.trans (hr i).1, (hr i).2⟩))
      (fun E' hE' => ih k hkd β b E' hβb hE')
    exact ⟨F, hF⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


/-! # Variable-exponent comparisons at a vanishing positive base

The affine-label construction uses exponent sequences rather than fixed
exponents. These lemmas justify comparison when the limiting exponents have a
strict gap, without replacing a variable power by the power of its limit.
-/

open Filter Asymptotics
open scoped Topology

namespace Problem326

variable {α : Type uAlpha} {l : Filter α} {h p q : α → ℝ} {a b : ℝ}

/-- A positive limiting exponent makes a power of a vanishing base vanish. -/
theorem tendsto_rpow_variable_zero
    (hh : Tendsto h l (𝓝 0)) (hp : Tendsto p l (𝓝 a)) (ha : 0 < a) :
    Tendsto (fun n => h n ^ p n) l (𝓝 0) := by
  simpa only [Real.zero_rpow ha.ne'] using hh.rpow hp (Or.inr ha)

/-- A strict limiting exponent gap gives a vanishing quotient of powers. -/
theorem tendsto_rpow_div_rpow_zero_of_gap
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b)) (hgap : b < a) :
    Tendsto (fun n => h n ^ p n / h n ^ q n) l (𝓝 0) := by
  have ht := tendsto_rpow_variable_zero hh (hp.sub hq) (sub_pos.mpr hgap)
  refine ht.congr' ?_
  filter_upwards [hpos] with n hn
  exact Real.rpow_sub hn (p n) (q n)

/-- Little-oh comparison remains valid for converging, variable exponents. -/
theorem isLittleO_rpow_variable_of_gap
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b)) (hgap : b < a) :
    (fun n => h n ^ p n) =o[l] (fun n => h n ^ q n) := by
  refine Asymptotics.isLittleO_of_tendsto' ?_
    (tendsto_rpow_div_rpow_zero_of_gap hpos hh hp hq hgap)
  filter_upwards [hpos] with n hn
  exact fun hz => False.elim ((Real.rpow_pos_of_pos hn (q n)).ne' hz)

/-- Reversing the strict limiting gap makes the quotient diverge to infinity. -/
theorem tendsto_rpow_div_rpow_atTop_of_gap
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b)) (hgap : a < b) :
    Tendsto (fun n => h n ^ p n / h n ^ q n) l atTop := by
  have hz := tendsto_rpow_div_rpow_zero_of_gap hpos hh hq hp hgap
  have hzpos : ∀ᶠ n in l, 0 < h n ^ q n / h n ^ p n := by
    filter_upwards [hpos] with n hn
    exact div_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hn _)
  have ht := (tendsto_nhdsWithin_iff.mpr ⟨hz, hzpos⟩).inv_tendsto_nhdsGT_zero
  change Tendsto (fun n => (h n ^ q n / h n ^ p n)⁻¹) l atTop at ht
  simpa only [inv_div] using ht

/-- Eventual domination of powers forces the reverse order on limiting exponents. -/
theorem exponent_le_of_eventually_rpow_le [NeBot l]
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b))
    {C : ℝ} (hbound : ∀ᶠ n in l, h n ^ p n ≤ C * h n ^ q n) :
    b ≤ a := by
  by_contra hnot
  have hgap : a < b := lt_of_not_ge hnot
  have hlarge := (tendsto_rpow_div_rpow_atTop_of_gap hpos hh hp hq hgap).eventually
    (eventually_gt_atTop C)
  obtain ⟨n, hnpos, hnle, hnlt⟩ := (hpos.and (hbound.and hlarge)).exists
  have hden : 0 < h n ^ q n := Real.rpow_pos_of_pos hnpos _
  exact (not_lt_of_ge ((div_le_iff₀ hden).mpr hnle)) hnlt

/-- The big-oh version of the limiting exponent obstruction. -/
theorem exponent_le_of_isBigO_rpow [NeBot l]
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b))
    (hbound : (fun n => h n ^ p n) =O[l] (fun n => h n ^ q n)) :
    b ≤ a := by
  obtain ⟨C, hC⟩ := hbound.bound
  apply exponent_le_of_eventually_rpow_le hpos hh hp hq (C := C)
  filter_upwards [hpos, hC] with n hn hCn
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _)] using hCn

/-- A positive leading power remains positive under a little-oh perturbation. -/
theorem eventually_pos_rpow_add_isLittleO {r : α → ℝ} {C : ℝ}
    (hpos : ∀ᶠ n in l, 0 < h n) (hC : 0 < C)
    (hr : r =o[l] (fun n => h n ^ q n)) :
    ∀ᶠ n in l, 0 < C * h n ^ q n + r n := by
  have he : ∀ᶠ n in l, -C < r n / h n ^ q n :=
    hr.tendsto_div_nhds_zero.eventually (lt_mem_nhds (neg_lt_zero.mpr hC))
  filter_upwards [hpos, he] with n hn hne
  have hden : 0 < h n ^ q n := Real.rpow_pos_of_pos hn _
  have hlt := (lt_div_iff₀ hden).mp hne
  linarith

/-- The corresponding negative leading term stays strictly negative. -/
theorem eventually_neg_neg_rpow_add_isLittleO {r : α → ℝ} {C : ℝ}
    (hpos : ∀ᶠ n in l, 0 < h n) (hC : 0 < C)
    (hr : r =o[l] (fun n => h n ^ q n)) :
    ∀ᶠ n in l, -C * h n ^ q n + r n < 0 := by
  have he := eventually_pos_rpow_add_isLittleO hpos hC hr.neg_left
  filter_upwards [he] with n hn
  linarith

/-- A finite linear combination of powers with larger limiting exponents is
little-oh of the comparison power. Coefficients need not be positive. -/
theorem isLittleO_sum_mul_rpow_variable_of_gap {ι : Type uIota}
    (s : Finset ι) (c : ι → ℝ) {p : α → ι → ℝ} {a : ι → ℝ}
    (hpos : ∀ᶠ n in l, 0 < h n) (hh : Tendsto h l (𝓝 0))
    (hp : ∀ i ∈ s, Tendsto (fun n => p n i) l (𝓝 (a i)))
    (hq : Tendsto q l (𝓝 b)) (hgap : ∀ i ∈ s, b < a i) :
    (fun n => ∑ i ∈ s, c i * h n ^ p n i) =o[l] (fun n => h n ^ q n) := by
  exact Asymptotics.IsLittleO.fun_sum fun i hi =>
    (isLittleO_rpow_variable_of_gap hpos hh (hp i hi) hq (hgap i hi)).const_mul_left (c i)

end Problem326

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.Affine

/-- Shift an affine label without changing its slope. -/
def Label.shiftOffset {d : ℕ} (L : Label d) (s : ℝ → ℝ) : Label d :=
  ⟨L.slope, fun h => L.offset h - s h⟩

@[simp] theorem Label.shiftOffset_slope {d : ℕ} (L : Label d) (s : ℝ → ℝ) :
    (L.shiftOffset s).slope = L.slope := rfl

@[simp] theorem Label.shiftOffset_value {d : ℕ} (L : Label d) (s : ℝ → ℝ)
    (h : ℝ) (x : Fin d → ℝ) :
    (L.shiftOffset s).value h x = L.value h x - s h := by
  simp only [Label.shiftOffset, Label.value]
  ring

/-- The finite union of shifted local families; duplicate labels are harmless. -/
def shiftedFamily {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ) : Finset (Label d) := by
  classical
  exact Finset.univ.biUnion (fun i => (Λ i).image (fun L => L.shiftOffset (s i)))

theorem mem_shiftedFamily_iff {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ) (J : Label d) :
    J ∈ shiftedFamily Λ s ↔ ∃ i, ∃ L ∈ Λ i, L.shiftOffset (s i) = J := by
  classical
  simp [shiftedFamily]

theorem shiftOffset_mem_shiftedFamily {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ)
    {i : ι} {L : Label d} (hL : L ∈ Λ i) :
    L.shiftOffset (s i) ∈ shiftedFamily Λ s :=
  (mem_shiftedFamily_iff Λ s _).mpr ⟨i, L, hL, rfl⟩

theorem active_shiftedFamily_restrict {d : ℕ} {ι : Type uIota} [Fintype ι]
    (Λ : ι → Finset (Label d)) (s : ι → ℝ → ℝ)
    {i : ι} {L : Label d} {h : ℝ} {x : Fin d → ℝ}
    (hL : L ∈ Λ i)
    (hA : Active (shiftedFamily Λ s) (L.shiftOffset (s i)) h x) :
    Active (Λ i) L h x := by
  refine ⟨hL, ?_⟩
  intro J hJ
  have hcomp := hA.2 (J.shiftOffset (s i)) (shiftOffset_mem_shiftedFamily Λ s hJ)
  simpa only [Label.shiftOffset_value, sub_le_sub_iff_right] using hcomp

/-- An arbitrary total extension is only used at valid cut indices. -/
def extendedCut {n : ℕ} (q : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then q ⟨k, hk⟩ else 0

@[simp] theorem extendedCut_fin {n : ℕ} (q : Fin n → ℝ) (i : Fin n) :
    extendedCut q i.val = q i := by simp [extendedCut, i.isLt]

/-- Cumulative shifts select a local family on the corresponding exponent cell. -/
def cutShift {n : ℕ} (q : Fin n → ℝ) (j : Fin (n + 1)) (h : ℝ) : ℝ :=
  ∑ k ∈ Finset.range j.val, h ^ extendedCut q k

/-- Closed cells include tied transition points. -/
def InCutCell {n : ℕ} (q : Fin n → ℝ) (a b : ℝ)
    (j : Fin (n + 1)) (μ : ℝ) : Prop :=
  a ≤ μ ∧ μ ≤ b ∧
    (∀ i : Fin n, i.castSucc = j → μ ≤ q i) ∧
    (∀ i : Fin n, i.succ = j → q i ≤ μ)

/-- Actual canonical label activity supplies the upper-cut inequality needed
by the asymptotic neighboring-family comparison. -/
theorem active_shiftedFamily_upper_cut {d n : ℕ}
    (Λ : Fin (n + 1) → Finset (Label d))
    (q : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (hbase : ∀ j, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (i : Fin n) {L : Label d}
    (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ)
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀))
    (hoff : L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hA : ∀ k, Active (shiftedFamily Λ (cutShift q))
      (L.shiftOffset (cutShift q i.castSucc)) (h k) (powerPoint (h k) (p k))) :
    ∃ k, p₀ k ≤ q i := by
  have hto : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Filter.Eventually.of_forall hpos⟩
  apply AffineGluing.shifted_active_upper_cut
    (x := fun j k => h k ^ p k j) (c := fun k => L.offset (h k))
    (fun j k => h k ^ extendedCut q j) L.slope p₀ (t i.succ) (q i) i.val
  · exact Filter.Eventually.of_forall (fun k => Real.rpow_pos_of_pos (hpos k) _)
  · simpa only [extendedCut_fin, Function.comp_def] using hoff.comp_tendsto hto
  · intro k hk
    simpa only [extendedCut_fin, Function.comp_def] using isLittleO_rpow_variable_of_gap
      (Filter.Eventually.of_forall hpos) hh
      (((continuous_apply k).tendsto p₀).comp hp) tendsto_const_nhds hk
  · apply Filter.Eventually.of_forall
    intro k
    have hc := (hA k).2
      ((⟨fun _ => t i.succ, fun _ => 0⟩ : Label d).shiftOffset (cutShift q i.succ))
      (shiftOffset_mem_shiftedFamily Λ (cutShift q) (hbase i.succ))
    simpa only [Label.shiftOffset, Label.value, powerPoint, cutShift,
      Fin.val_succ, Fin.val_castSucc, add_zero, zero_add, zero_sub, sub_eq_add_neg, add_assoc] using hc

/-- The corresponding lower-cut conclusion, using the strict slope gap to
the preceding baseline. -/
theorem active_shiftedFamily_lower_cut {d n : ℕ}
    (Λ : Fin (n + 1) → Finset (Label d))
    (q : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (hbase : ∀ j, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (i : Fin n) {L : Label d} (hr : ∀ k, t i.castSucc < L.slope k)
    (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ)
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 p₀))
    (hoff : L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hA : ∀ k, Active (shiftedFamily Λ (cutShift q))
      (L.shiftOffset (cutShift q i.succ)) (h k) (powerPoint (h k) (p k))) :
    ∀ k, q i ≤ p₀ k := by
  have hto : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Filter.Eventually.of_forall hpos⟩
  apply AffineGluing.shifted_active_lower_cut
    (x := fun j k => h k ^ p k j) (c := fun k => L.offset (h k))
    (fun j k => h k ^ extendedCut q j) L.slope p₀ (t i.castSucc) (q i) i.val hr
  · exact Filter.Eventually.of_forall (fun k => Real.rpow_pos_of_pos (hpos k) _)
  · simpa only [extendedCut_fin, Function.comp_def] using hoff.comp_tendsto hto
  · exact Filter.Eventually.of_forall
      (fun k j => (Real.rpow_pos_of_pos (hpos k) (p k j)).le)
  · intro k hk
    simpa only [extendedCut_fin, Function.comp_def] using tendsto_rpow_div_rpow_atTop_of_gap
      (Filter.Eventually.of_forall hpos) hh
      (((continuous_apply k).tendsto p₀).comp hp) tendsto_const_nhds hk
  · apply Filter.Eventually.of_forall
    intro k
    have hc := (hA k).2
      ((⟨fun _ => t i.castSucc, fun _ => 0⟩ : Label d).shiftOffset (cutShift q i.castSucc))
      (shiftOffset_mem_shiftedFamily Λ (cutShift q) (hbase i.castSucc))
    simpa only [Label.shiftOffset, Label.value, powerPoint, cutShift,
      Fin.val_succ, Fin.val_castSucc, add_zero, zero_add, zero_sub, sub_eq_add_neg, add_assoc] using hc

/-- Assemble the global sequential approximation statement from local cell
statements. All activity is activity of the actual finite union of shifted
canonical labels; no analytically unsupported preferred minimizer is selected. -/
theorem approximatesOnCube_shiftedFamily_of_cells {d n : ℕ} [NeZero d]
    (Λ : Fin (n + 1) → Finset (Label d))
    (q : Fin n → ℝ) (t : Fin (n + 1) → ℝ)
    (a b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (ht : StrictMono t)
    (hbase : ∀ j, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (hslope : ∀ j, ∀ L ∈ Λ j, ∀ k, t j ≤ L.slope k)
    (hoffUpper : ∀ i : Fin n, ∀ L ∈ Λ i.castSucc,
      L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hoffLower : ∀ i : Fin n, ∀ L ∈ Λ i.succ,
      L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ q i))
    (hlocal : ∀ j, ∀ L ∈ Λ j,
      ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
      (∀ k, 0 < h k) → Tendsto h atTop (𝓝 0) →
      Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
      InCutCell q a b j (coordinateMinimum p₀) →
      (∀ k, Active (Λ j) L (h k) (powerPoint (h k) (p k))) →
      ‖p₀ - L.slope‖ < E L.slope) :
    ApproximatesOnCube (shiftedFamily Λ (cutShift q)) a b E := by
  intro J hJ h p p₀ hpos hh hp hcube hA
  obtain ⟨j, L, hL, rfl⟩ := (mem_shiftedFamily_iff Λ (cutShift q) J).mp hJ
  change ‖p₀ - L.slope‖ < E L.slope
  apply hlocal j L hL h p p₀ hpos hh hp hcube
  · have hm := hasMinimum_coordinateMinimum p₀
    obtain ⟨k, hk⟩ := hm.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hk]
      exact (hcube k).1
    · rw [← hk]
      exact (hcube k).2
    · intro i hij
      subst j
      obtain ⟨k, hki⟩ := active_shiftedFamily_upper_cut Λ q t hbase i
        h p p₀ hpos hh hp (hoffUpper i L hL) hA
      exact (hm.1 k).trans hki
    · intro i hij
      subst j
      have hr : ∀ k, t i.castSucc < L.slope k := fun k =>
        (ht (by simp : i.castSucc < i.succ)).trans_le (hslope i.succ L hL k)
      have hki := active_shiftedFamily_lower_cut Λ q t hbase i hr
        h p p₀ hpos hh hp (hoffLower i L hL) hA
      rw [← hk]
      exact hki k
  · intro k
    exact active_shiftedFamily_restrict Λ (cutShift q) hL (hA k)

/-- Every cumulative cut shift is negligible at the original lower exponent. -/
theorem cutShift_isLittleO {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ i, a < q i) (j : Fin (n + 1)) :
    cutShift q j =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
  unfold cutShift
  apply IsLittleO.fun_sum
  intro k hk
  have hkj : k < j.val := Finset.mem_range.mp hk
  have hkn : k < n := lt_of_lt_of_le hkj (Nat.le_of_lt_succ j.isLt)
  have hpow := isLittleO_rpow_variable_of_gap
    (h := fun h : ℝ => h) (l := 𝓝[>] (0 : ℝ))
    (show ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h from self_mem_nhdsWithin)
    (show Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
    (tendsto_const_nhds (x := q ⟨k, hkn⟩)) (tendsto_const_nhds (x := a)) (hq ⟨k, hkn⟩)
  simpa only [extendedCut, dite_eq_left hkn] using hpow

/-- The union stays nonempty, preserves slope bounds, and preserves the
required offset decay after all cumulative shifts. -/
theorem shiftedFamily_properties {d n : ℕ}
    (Λ : Fin (n + 1) → Finset (Label d)) (q : Fin n → ℝ) (a b : ℝ)
    (hne : (Λ 0).Nonempty)
    (hslopes : ∀ j, ∀ L ∈ Λ j, Cube a b L.slope)
    (hoff : ∀ j, ∀ L ∈ Λ j, L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a))
    (hq : ∀ i, a < q i) :
    (shiftedFamily Λ (cutShift q)).Nonempty ∧
      ∀ J ∈ shiftedFamily Λ (cutShift q), Cube a b J.slope ∧
        J.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
  constructor
  · obtain ⟨L, hL⟩ := hne
    exact ⟨L.shiftOffset (cutShift q 0), shiftOffset_mem_shiftedFamily Λ (cutShift q) hL⟩
  · intro J hJ
    obtain ⟨j, L, hL, rfl⟩ := (mem_shiftedFamily_iff Λ (cutShift q) J).mp hJ
    exact ⟨hslopes j L hL, (hoff j L hL).sub (cutShift_isLittleO q a hq j)⟩

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.Affine

/-- The closed cell between neighboring cuts is contained in the corresponding
open localization neighborhood, including all endpoint and tie cases. -/
theorem InCutCell.abs_sub_lt {n : ℕ} {q : Fin n → ℝ}
    {a b : ℝ} {t ρ : Fin (n + 1) → ℝ}
    (hfirst : t 0 - ρ 0 < a)
    (hlast : b < t (Fin.last n) + ρ (Fin.last n))
    (hcuts : ∀ i : Fin n,
      q i ∈ Set.Ioo (t i.castSucc - ρ i.castSucc) (t i.castSucc + ρ i.castSucc) ∧
      q i ∈ Set.Ioo (t i.succ - ρ i.succ) (t i.succ + ρ i.succ))
    {j : Fin (n + 1)} {μ : ℝ} (hcell : InCutCell q a b j μ) :
    |μ - t j| < ρ j := by
  apply abs_lt.mpr
  have hlo : t j - ρ j < μ := by
    by_cases hj : j = 0
    · subst j
      exact hfirst.trans_le hcell.1
    · have hjpos : 0 < j.val := by
        have hjne : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj
        omega
      let i : Fin n := ⟨j.val - 1, by omega⟩
      have hij : i.succ = j := by apply Fin.ext; dsimp [i]; omega
      have hq := (hcuts i).2.1
      rw [hij] at hq
      exact hq.trans_le (hcell.2.2.2 i hij)
  have hhi : μ < t j + ρ j := by
    by_cases hj : j = Fin.last n
    · subst j
      exact hcell.2.1.trans_lt hlast
    · have hjlt : j.val < n := by
        have hjne : j.val ≠ n := by simpa only [Fin.ext_iff, Fin.val_last] using hj
        omega
      let i : Fin n := ⟨j.val, hjlt⟩
      have hij : i.castSucc = j := by apply Fin.ext; rfl
      have hq := (hcuts i).1.2
      rw [hij] at hq
      exact (hcell.2.2.1 i hij).trans_lt hq
  constructor <;> linarith

/-- All data needed from one fixed-minimum construction after its localization
radius has been shrunk to retain a stronger offset decay exponent. -/
structure LocalFamilyData (d : ℕ) [NeZero d] (a b t : ℝ)
    (E : (Fin d → ℝ) → ℝ) where
  family : Finset (Label d)
  radius : ℝ
  radius_pos : 0 < radius
  baseline_mem : (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ family
  slope_cube : ∀ L ∈ family, Cube a b L.slope
  slope_lower : ∀ L ∈ family, ∀ k, t ≤ L.slope k
  offset_decay : ∀ L ∈ family,
    L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ (t + radius))
  approximates_near : ∀ L ∈ family,
    ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ k, 0 < h k) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    |coordinateMinimum p₀ - t| < radius →
    (∀ k, Active family L (h k) (powerPoint (h k) (p k))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- The fixed-minimum theorem and stronger individual big-O exponents supply
exactly the local data required for global gluing. -/
theorem localFamilyData_nonempty_of_fixedMinimum {d : ℕ} [NeZero d]
    (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) (Λ : Finset (Label d))
    (hbase : (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Λ)
    (hcube : ∀ L ∈ Λ, Cube a b L.slope)
    (hlower : ∀ L ∈ Λ, ∀ k, t ≤ L.slope k)
    (hdecay : ∀ L ∈ Λ, ∃ β : ℝ, t < β ∧
      L.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β))
    (happrox : ApproximatesAtMinimum Λ a b t E) :
    Nonempty (LocalFamilyData d a b t E) := by
  classical
  obtain ⟨ρ₀, hρ₀, hnear⟩ := happrox.exists_nearby
  let : Nonempty ↥Λ := ⟨⟨_, hbase⟩⟩
  obtain ⟨ρ, hρ, hρsmall, hρdecay⟩ := exists_radius_with_offset_decay
    (fun L : Λ => L.val.offset) t ρ₀ hρ₀ (fun L => hdecay L.val L.property)
  refine ⟨⟨Λ, ρ, hρ, hbase, hcube, hlower, ?_, ?_⟩⟩
  · intro L hL
    exact hρdecay ⟨L, hL⟩
  · intro L hL h p p₀ hpos hh hp hp₀ hclose hactive
    exact hnear L hL h p p₀ hpos hh hp hp₀ (hclose.trans hρsmall) hactive

/-- A convenient strict-power comparison for offset decay. -/
theorem offset_isLittleO_of_exponent_lt {c : ℝ → ℝ} {a b : ℝ}
    (hc : c =o[𝓝[>] (0 : ℝ)] (fun h => h ^ b)) (hab : a < b) :
    c =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
  apply hc.trans
  exact isLittleO_rpow_variable_of_gap
    (h := fun h : ℝ => h) (l := 𝓝[>] (0 : ℝ))
    (show ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h from self_mem_nhdsWithin)
    (show Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
    tendsto_const_nhds tendsto_const_nhds hab

/-- Complete global gluing: one localized family at every possible minimum
level gives a fixed finite family on the whole exponent cube. The only input
not discharged here is existence of the fixed-minimum local families. -/
theorem exists_global_family_of_local_data {d : ℕ} [NeZero d]
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hdata : ∀ t ∈ Set.Icc a b, Nonempty (LocalFamilyData d a b t E)) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a)) ∧
      ApproximatesOnCube Λ a b E := by
  classical
  let D : (t : {t : ℝ // t ∈ Set.Icc a b}) → LocalFamilyData d a b t.val E :=
    fun t => Classical.choice (hdata t.val t.property)
  let r : ℝ → ℝ := fun t => if ht : t ∈ Set.Icc a b then (D ⟨t, ht⟩).radius else 1
  have hr : ∀ t ∈ Set.Icc a b, 0 < r t := by
    intro t ht
    simpa only [r, dite_eq_left ht] using (D ⟨t, ht⟩).radius_pos
  obtain ⟨n, t, q, ht, hcent, hfirst, hlast, hcuts⟩ :=
    IntervalGluing.exists_interval_gluing hab r hr
  let F : (j : Fin (n + 1)) → LocalFamilyData d a b (t j) E :=
    fun j => D ⟨t j, hcent j⟩
  let Γ : Fin (n + 1) → Finset (Label d) := fun j => (F j).family
  have hrF : ∀ j, r (t j) = (F j).radius := by
    intro j
    simp only [r, dite_eq_left (hcent j), F]
  have hcutmem : ∀ i : Fin n,
      q i ∈ Set.Ioo (t i.castSucc - (F i.castSucc).radius)
        (t i.castSucc + (F i.castSucc).radius) ∧
      q i ∈ Set.Ioo (t i.succ - (F i.succ).radius)
        (t i.succ + (F i.succ).radius) := by
    intro i
    simpa only [hrF] using (hcuts i).2.2
  have hinitial : t 0 - (F 0).radius < a := by
    simpa only [hrF] using hfirst.1
  have hfinal : b < t (Fin.last n) + (F (Fin.last n)).radius := by
    simpa only [hrF] using hlast.2
  have hqa : ∀ i : Fin n, a < q i :=
    fun i => (hcent i.castSucc).1.trans_lt (hcuts i).1
  have hdecay : ∀ j, ∀ L ∈ Γ j,
      L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a) := by
    intro j L hL
    apply offset_isLittleO_of_exponent_lt ((F j).offset_decay L hL)
    have htja := (hcent j).1
    have hrad := (F j).radius_pos
    linarith
  have hprop := shiftedFamily_properties Γ q a b
    ⟨_, (F 0).baseline_mem⟩
    (fun j L hL => (F j).slope_cube L hL) hdecay hqa
  refine ⟨shiftedFamily Γ (cutShift q), hprop.1, hprop.2, ?_⟩
  apply approximatesOnCube_shiftedFamily_of_cells Γ q t a b E ht
    (fun j => (F j).baseline_mem) (fun j L hL => (F j).slope_lower L hL)
  · intro i L hL
    exact offset_isLittleO_of_exponent_lt ((F i.castSucc).offset_decay L hL)
      (hcutmem i).1.2
  · intro i L hL
    exact offset_isLittleO_of_exponent_lt ((F i.succ).offset_decay L hL)
      (hcutmem i).2.2
  · intro j L hL h p p₀ hpos hh hp hcube hcell hactive
    exact (F j).approximates_near L hL h p p₀ hpos hh hp hcube
      (InCutCell.abs_sub_lt (t := t) (ρ := fun j => (F j).radius) hinitial hfinal hcutmem hcell) hactive

/-- Direct interface for the dimension induction: fixed-minimum families with
individual stronger big-O exponents imply the complete affine approximation
lemma in that dimension. -/
theorem exists_global_family_of_fixedMinimum {d : ℕ} [NeZero d]
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hfixed : ∀ t ∈ Set.Icc a b, ∃ Λ : Finset (Label d),
      (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Λ ∧
      (∀ L ∈ Λ, Cube a b L.slope) ∧
      (∀ L ∈ Λ, ∀ k, t ≤ L.slope k) ∧
      (∀ L ∈ Λ, ∃ β : ℝ, t < β ∧
        L.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β)) ∧
      ApproximatesAtMinimum Λ a b t E) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ a)) ∧
      ApproximatesOnCube Λ a b E := by
  apply exists_global_family_of_local_data hab E
  intro t ht
  obtain ⟨Λ, hbase, hcube, hlower, hdecay, happrox⟩ := hfixed t ht
  exact localFamilyData_nonempty_of_fixedMinimum a b t E Λ hbase hcube hlower hdecay happrox

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326.Affine

/-- The complete gluing argument in the exact certificate interface consumed by
`fullCertificate_of_local_and_glue`. No gluing assumption remains in this theorem. -/
theorem fullCertificate_glue
    (d : ℕ) (hd : 0 < d) (a b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (hab : a < b) (_hE : ∀ r, Cube a b r → 0 < E r)
    (hlocal : ∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E)) :
    Nonempty (FullCertificate d a b E) := by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨Λ, hne, hprop, happ⟩ := exists_global_family_of_fixedMinimum hab.le E (by
    intro t ht
    let C := Classical.choice (hlocal t ht.1 ht.2)
    refine ⟨C.labels, C.baseline, ?_, ?_, ?_, C.approximation⟩
    · intro L hL i
      exact ⟨ht.1.trans (C.slopes L hL i).1, (C.slopes L hL i).2⟩
    · intro L hL i
      exact (C.slopes L hL i).1
    · intro L hL
      exact ⟨C.decayExponent, C.decay_gt, (C.offsets L hL).isBigO⟩)
  exact ⟨{
    labels := Λ
    nonempty := hne
    slopes := fun L hL => (hprop L hL).1
    offsets := fun L hL => (hprop L hL).2
    approximation := happ
  }⟩

/-- The full affine approximation theorem now reduces solely to constructing
fixed-minimum certificates from lower-dimensional full certificates. -/
theorem fullCertificate_of_local_constructor
    (construct : ∀ d : ℕ, 0 < d →
      (∀ k : ℕ, k < d → ∀ a b : ℝ, ∀ E : (Fin k → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate k a b E)) →
      ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
        a < b → (∀ r, Cube a b r → 0 < E r) →
        ∀ t : ℝ, a ≤ t → t ≤ b → Nonempty (LocalCertificate d a b t E)) :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) → Nonempty (FullCertificate d a b E) :=
  fullCertificate_of_local_and_glue construct fullCertificate_glue

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326.Affine

/-- Full arbitrary-tolerance affine approximation, with both the dimension
induction and the finite interval gluing discharged. -/
theorem fullCertificate_exists :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate d a b E) :=
  fullCertificate_of_local_constructor localCertificate_of_lower_fullCertificates

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI


open Set

namespace Problem326

/-- A continuous curve cannot first leave a closed region if every initial segment
inside the region ends in a fixed subset of its interior. -/
theorem mapsTo_interior_of_initial_segments {X : Type uX} [TopologicalSpace X]
    {x : ℝ → X} {a b : ℝ} {B K : Set X}
    (hB : IsClosed B) (hK : K ⊆ interior B)
    (hc : ContinuousOn x (Icc a b)) (ha : x a ∈ interior B)
    (htrap : ∀ t ∈ Icc a b, MapsTo x (Icc a t) B → x t ∈ K) :
    MapsTo x (Icc a b) (interior B) := by
  intro t ht
  by_contra hxt
  let S := Icc a b ∩ x ⁻¹' (interior B)ᶜ
  have hS : IsClosed S :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
  have hSne : S.Nonempty := ⟨t, ht, hxt⟩
  have hSbelow : BddBelow S := ⟨a, fun u hu => hu.1.1⟩
  obtain ⟨hτ, hleast⟩ := hS.isLeast_csInf hSne hSbelow
  let τ := sInf S
  have hτab : τ ∈ Icc a b := hτ.1
  have hτbad : x τ ∉ interior B := hτ.2
  have haτ : a < τ := by
    apply lt_of_le_of_ne hτab.1
    intro he
    exact hτbad (he ▸ ha)
  have hgood : Ico a τ ⊆ Icc a b ∩ x ⁻¹' B := by
    intro u hu
    have huab : u ∈ Icc a b := ⟨hu.1, hu.2.le.trans hτab.2⟩
    refine ⟨huab, ?_⟩
    change x u ∈ B
    apply interior_subset
    by_contra hxu
    have huS : u ∈ S := ⟨huab, hxu⟩
    exact (not_le_of_gt hu.2) (hleast huS)
  have hclosed : IsClosed (Icc a b ∩ x ⁻¹' B) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc hB
  have hsegment : Icc a τ ⊆ Icc a b ∩ x ⁻¹' B := by
    rw [← closure_Ico haτ.ne]
    exact closure_minimal hgood hclosed
  have hτK : x τ ∈ K := htrap τ hτab (fun u hu => (hsegment hu).2)
  exact hτbad (hK hτK)

/-- Endpoint trapping on every initial segment upgrades to trapping on the entire
closed interval once the trapping set lies strictly inside the closed region. -/
theorem mapsTo_of_initial_segments {X : Type uX} [TopologicalSpace X]
    {x : ℝ → X} {a b : ℝ} {B K : Set X}
    (hB : IsClosed B) (hK : K ⊆ interior B)
    (hc : ContinuousOn x (Icc a b)) (ha : x a ∈ interior B)
    (htrap : ∀ t ∈ Icc a b, MapsTo x (Icc a t) B → x t ∈ K) :
    MapsTo x (Icc a b) K := by
  have hint := mapsTo_interior_of_initial_segments hB hK hc ha htrap
  intro t ht
  apply htrap t ht
  intro u hu
  exact interior_subset (hint ⟨hu.1, hu.2.trans ht.2⟩)

end Problem326

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped Topology

namespace Problem326

/-- Compatible differentiable curves on an open cover glue to one curve.
 The vector field may depend on time, and ordinary two-sided derivatives
 are preserved at all points. -/
theorem glue_hasDerivAt_of_open_cover {ι : Type uIota} {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : ι → Set ℝ) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ t, ∃ i, t ∈ U i) (curve : ι → ℝ → E)
    (hcompat : ∀ i j, Set.EqOn (curve i) (curve j) (U i ∩ U j))
    (v : ℝ → E → E)
    (hderiv : ∀ i t, t ∈ U i → HasDerivAt (curve i) (v t (curve i t)) t) :
    ∃ x : ℝ → E, (∀ i, Set.EqOn x (curve i) (U i)) ∧
      ∀ t, HasDerivAt x (v t (x t)) t := by
  choose index hindex using hcover
  let x : ℝ → E := fun t => curve (index t) t
  have hx : ∀ i, Set.EqOn x (curve i) (U i) := by
    intro i t ht
    exact hcompat (index t) i ⟨hindex t, ht⟩
  refine ⟨x, hx, ?_⟩
  intro t
  let i := index t
  have ht : t ∈ U i := hindex t
  have heq : x =ᶠ[𝓝 t] curve i :=
    (show ∀ᶠ s in 𝓝 t, s ∈ U i from (hopen i).mem_nhds ht).mono
      (fun s hs => hx i hs)
  rw [hx i ht]
  exact (hderiv i t ht).congr_of_eventuallyEq heq

/-- A family on expanding symmetric intervals is an open cover of real time. -/
theorem symmetric_intervals_cover (t : ℝ) :
    ∃ n : ℕ, t ∈ Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  refine ⟨n, ?_, ?_⟩
  · have := neg_abs_le t
    linarith
  · have := le_abs_self t
    linarith

/-- The countable-interval specialization used to globalize finite-horizon ODE
 solutions without losing differentiability at time zero. -/
theorem glue_hasDerivAt_on_symmetric_intervals {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (curve : ℕ → ℝ → E) (v : ℝ → E → E)
    (hcompat : ∀ m n, Set.EqOn (curve m) (curve n)
      (Set.Ioo (-(m : ℝ) - 1) ((m : ℝ) + 1) ∩
       Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1)))
    (hderiv : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1) →
      HasDerivAt (curve n) (v t (curve n t)) t) :
    ∃ x : ℝ → E,
      (∀ n, Set.EqOn x (curve n) (Set.Ioo (-(n : ℝ) - 1) ((n : ℝ) + 1))) ∧
      ∀ t, HasDerivAt x (v t (x t)) t :=
  glue_hasDerivAt_of_open_cover _ (fun _ => isOpen_Ioo)
    symmetric_intervals_cover curve hcompat v hderiv

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326.IntervalChain

/-- A finite cover can be reduced so that no selected set is contained in
another selected set. -/
theorem exists_irredundant_subcover {ι : Type uIota} {X : Type uX}
    (s : Finset ι) (U : ι → Set X) (K : Set X)
    (hcover : ∀ x ∈ K, ∃ i ∈ s, x ∈ U i) :
    ∃ t : Finset ι, t ⊆ s ∧
      (∀ x ∈ K, ∃ i ∈ t, x ∈ U i) ∧
      ∀ i ∈ t, ∀ j ∈ t, i ≠ j → ¬ U i ⊆ U j := by
  classical
  let P : Finset ι → Prop := fun t => t ⊆ s ∧ ∀ x ∈ K, ∃ i ∈ t, x ∈ U i
  obtain ⟨t, ht⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card ⟨s, ⟨by rfl, hcover⟩⟩
  refine ⟨t, ht.prop.1, ht.prop.2, ?_⟩
  intro i hi j hj hij hsub
  have herase : P (t.erase i) := by
    refine ⟨(Finset.erase_subset i t).trans ht.prop.1, ?_⟩
    intro x hx
    obtain ⟨k, hk, hxk⟩ := ht.prop.2 x hx
    by_cases hki : k = i
    · subst k
      exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hsub hxk⟩
    · exact ⟨k, Finset.mem_erase.mpr ⟨hki, hk⟩, hxk⟩
  exact ht.not_lt herase (Finset.card_erase_lt_of_mem hi)

/-- Compactness supplies finitely many centers from the original interval. -/
theorem exists_finite_center_cover {a b : ℝ} (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ s : Finset ℝ,
      (∀ t ∈ s, t ∈ Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t) := by
  classical
  have hcover : Set.Icc a b ⊆
      ⋃ t ∈ Set.Icc a b, Set.Ioo (t - ρ t) (t + ρ t) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    have hp := hρ x hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hfin, hcov⟩ := isCompact_Icc.elim_finite_subcover_image
    (fun t ht => isOpen_Ioo) hcover
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro t ht
    exact hs (hfin.mem_toFinset.mp ht)
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact ⟨t, hfin.mem_toFinset.mpr ht, hxt⟩

/-- Noncontainment forces the interval endpoints to be ordered in the same
way as their centers. -/
theorem endpoints_strictMono {u v ru rv : ℝ}
    (huv : u < v)
    (hnot : ¬ Set.Ioo (u - ru) (u + ru) ⊆ Set.Ioo (v - rv) (v + rv))
    (hnot' : ¬ Set.Ioo (v - rv) (v + rv) ⊆ Set.Ioo (u - ru) (u + ru)) :
    u - ru < v - rv ∧ u + ru < v + rv := by
  constructor
  · by_contra h
    have hl : v - rv ≤ u - ru := le_of_not_gt h
    apply hnot
    intro x hx
    exact ⟨lt_of_le_of_lt hl hx.1, by linarith [hx.2]⟩
  · by_contra h
    have hr : v + rv ≤ u + ru := le_of_not_gt h
    apply hnot'
    intro x hx
    exact ⟨by linarith [hx.1], lt_of_lt_of_le hx.2 hr⟩

/-- Successive selected intervals overlap when their union covers the
whole interval and their endpoint order follows their center order. -/
theorem adjacent_overlap {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hcenters : ∀ t ∈ s, t ∈ Set.Icc a b)
    (hρ : ∀ t ∈ s, 0 < ρ t)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t))
    (horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v)
    {u v : ℝ} (hu : u ∈ s) (hv : v ∈ s) (huv : u < v)
    (hadj : ∀ w ∈ s, u < w → v ≤ w) :
    v - ρ v < u + ρ u := by
  by_contra h
  have hgap : u + ρ u ≤ v - ρ v := le_of_not_gt h
  have hx : u + ρ u ∈ Set.Icc a b := by
    have hu' := hcenters u hu
    have hv' := hcenters v hv
    have hru := hρ u hu
    have hrv := hρ v hv
    constructor <;> linarith [hu'.1, hv'.2]
  obtain ⟨w, hw, hxw⟩ := hcover (u + ρ u) hx
  rcases lt_trichotomy w u with hwu | rfl | huw
  · have hord := (horder w hw u hu hwu).2
    linarith [hxw.2]
  · exact (lt_irrefl _ hxw.2)
  · have hvw := hadj w hw huw
    rcases hvw.eq_or_lt with rfl | hvw
    · linarith [hxw.1]
    · have hord := (horder v hv w hw hvw).1
      linarith [hxw.1]

/-- An overlapping pair admits a transition cut in both neighborhoods and
strictly between the two centers. -/
theorem exists_transition_cut {u v ru rv : ℝ}
    (huv : u < v) (hru : 0 < ru) (hrv : 0 < rv)
    (hoverlap : v - rv < u + ru) :
    ∃ q : ℝ, u < q ∧ q < v ∧
      q ∈ Set.Ioo (u - ru) (u + ru) ∧
      q ∈ Set.Ioo (v - rv) (v + rv) := by
  have h : max u (v - rv) < min v (u + ru) := by
    apply max_lt
    · exact lt_min huv (by linarith)
    · exact lt_min (by linarith) hoverlap
  obtain ⟨q, hlo, hhi⟩ := exists_between h
  have huq : u < q := lt_of_le_of_lt (le_max_left _ _) hlo
  have hvq : v - rv < q := lt_of_le_of_lt (le_max_right _ _) hlo
  have hqv : q < v := lt_of_lt_of_le hhi (min_le_left _ _)
  have hqu : q < u + ru := lt_of_lt_of_le hhi (min_le_right _ _)
  exact ⟨q, huq, hqv, ⟨by linarith, hqu⟩, ⟨hvq, by linarith⟩⟩

/-- The first selected neighborhood contains the left endpoint. -/
theorem left_endpoint_mem {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hab : a ≤ b)
    (hcenters : ∀ t ∈ s, t ∈ Set.Icc a b)
    (hρ : ∀ t ∈ s, 0 < ρ t)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t))
    (horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v)
    {u : ℝ} (hu : u ∈ s) (hmin : ∀ w ∈ s, u ≤ w) :
    a ∈ Set.Ioo (u - ρ u) (u + ρ u) := by
  obtain ⟨w, hw, haw⟩ := hcover a ⟨le_rfl, hab⟩
  have hru := hρ u hu
  have hau := (hcenters u hu).1
  constructor
  · rcases (hmin w hw).eq_or_lt with rfl | huw
    · exact haw.1
    · exact ((horder u hu w hw huw).1).trans haw.1
  · linarith

/-- The last selected neighborhood contains the right endpoint. -/
theorem right_endpoint_mem {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hab : a ≤ b)
    (hcenters : ∀ t ∈ s, t ∈ Set.Icc a b)
    (hρ : ∀ t ∈ s, 0 < ρ t)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ t ∈ s, x ∈ Set.Ioo (t - ρ t) (t + ρ t))
    (horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v)
    {v : ℝ} (hv : v ∈ s) (hmax : ∀ w ∈ s, w ≤ v) :
    b ∈ Set.Ioo (v - ρ v) (v + ρ v) := by
  obtain ⟨w, hw, hbw⟩ := hcover b ⟨hab, le_rfl⟩
  have hrv := hρ v hv
  have hvb := (hcenters v hv).2
  constructor
  · linarith
  · rcases (hmax w hw).eq_or_lt with rfl | hwv
    · exact hbw.2
    · exact hbw.2.trans (horder w hw v hv hwv).2

/-- Assemble ordered centers and transition cuts. The endpoint and overlap
conditions imply each closed interval between neighboring cuts lies in its
assigned neighborhood. -/
theorem exists_interval_chain {a b : ℝ} (hab : a ≤ b) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ n : ℕ, ∃ c : Fin (n + 1) → ℝ, ∃ q : Fin n → ℝ,
      StrictMono c ∧ (∀ i, c i ∈ Set.Icc a b) ∧
      a ∈ Set.Ioo (c 0 - ρ (c 0)) (c 0 + ρ (c 0)) ∧
      b ∈ Set.Ioo (c (Fin.last n) - ρ (c (Fin.last n)))
        (c (Fin.last n) + ρ (c (Fin.last n))) ∧
      ∀ i : Fin n, c i.castSucc < q i ∧ q i < c i.succ ∧
        q i ∈ Set.Ioo (c i.castSucc - ρ (c i.castSucc))
          (c i.castSucc + ρ (c i.castSucc)) ∧
        q i ∈ Set.Ioo (c i.succ - ρ (c i.succ))
          (c i.succ + ρ (c i.succ)) := by
  classical
  obtain ⟨s₀, hs₀, hcover₀⟩ := exists_finite_center_cover ρ hρ
  obtain ⟨s, hsub, hcover, hirr⟩ := exists_irredundant_subcover s₀
    (fun t => Set.Ioo (t - ρ t) (t + ρ t)) (Set.Icc a b) hcover₀
  have hcenters : ∀ t ∈ s, t ∈ Set.Icc a b := fun t ht => hs₀ t (hsub ht)
  have hrad : ∀ t ∈ s, 0 < ρ t := fun t ht => hρ t (hcenters t ht)
  have horder : ∀ u ∈ s, ∀ v ∈ s, u < v →
      u - ρ u < v - ρ v ∧ u + ρ u < v + ρ v := by
    intro u hu v hv huv
    exact endpoints_strictMono huv (hirr u hu v hv huv.ne)
      (hirr v hv u hu huv.ne')
  have hsne : s.Nonempty := by
    obtain ⟨t, ht, _⟩ := hcover a ⟨le_rfl, hab⟩
    exact ⟨t, ht⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hsne)
  let c : Fin (n + 1) ↪o ℝ := s.orderEmbOfFin hn
  have hcmem : ∀ i, c i ∈ s := fun i => s.orderEmbOfFin_mem hn i
  have hcsurj : ∀ w ∈ s, ∃ i, c i = w := by
    intro w hw
    have hw' : w ∈ Set.range (s.orderEmbOfFin hn) := by
      rw [s.range_orderEmbOfFin hn]
      exact hw
    exact hw'
  have hcuts : ∀ i : Fin n, ∃ q : ℝ,
      c i.castSucc < q ∧ q < c i.succ ∧
      q ∈ Set.Ioo (c i.castSucc - ρ (c i.castSucc))
        (c i.castSucc + ρ (c i.castSucc)) ∧
      q ∈ Set.Ioo (c i.succ - ρ (c i.succ))
        (c i.succ + ρ (c i.succ)) := by
    intro i
    have hi : c i.castSucc < c i.succ := c.strictMono (by simp)
    apply exists_transition_cut hi (hrad _ (hcmem _)) (hrad _ (hcmem _))
    apply adjacent_overlap hcenters hrad hcover horder (hcmem _) (hcmem _) hi
    intro w hw hiw
    obtain ⟨k, rfl⟩ := hcsurj w hw
    apply c.monotone
    have hik : i.castSucc < k := c.lt_iff_lt.mp hiw
    change i.val + 1 ≤ k.val
    exact hik
  choose q hq using hcuts
  refine ⟨n, c, q, c.strictMono, (fun i => hcenters _ (hcmem i)), ?_, ?_, hq⟩
  · apply left_endpoint_mem hab hcenters hrad hcover horder (hcmem 0)
    intro w hw
    obtain ⟨k, rfl⟩ := hcsurj w hw
    exact c.monotone (Fin.zero_le k)
  · apply right_endpoint_mem hab hcenters hrad hcover horder (hcmem (Fin.last n))
    intro w hw
    obtain ⟨k, rfl⟩ := hcsurj w hw
    exact c.monotone (Fin.le_last k)

end Problem326.IntervalChain

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set

namespace Problem326.Affine

/-- The comparison-based activity convention agrees with attaining the finite
minimum, including every tied branch. -/
theorem active_iff_value_eq_inf {d : ℕ} {Λ : Finset (Label d)}
    (hne : Λ.Nonempty) {L : Label d} {h : ℝ} {z : Fin d → ℝ} :
    Active Λ L h z ↔
      L ∈ Λ ∧ L.value h z = Λ.inf' hne (fun J => J.value h z) := by
  constructor
  · intro hL
    exact ⟨hL.1, le_antisymm ((Finset.le_inf'_iff hne (fun J => J.value h z)).2 hL.2)
      (Finset.inf'_le _ hL.1)⟩
  · rintro ⟨hL, heq⟩
    refine ⟨hL, fun J hJ => ?_⟩
    rw [heq]
    exact Finset.inf'_le _ hJ

/-- Canonical affine labels directly supply the finite-interval trapping
principle. Only active slopes inside the closed region need point inward. -/
theorem trapped_of_active_inward
    {d : ℕ} (Λ : Finset (Label d)) (hne : Λ.Nonempty) (h : ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {T M : ℝ}
    (hT : 0 ≤ T) (hclosed : IsClosed B)
    (hx : ContinuousOn x (Icc 0 T))
    (hxd : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hx0 : x 0 ∈ interior B)
    (hinward : ∀ z ∈ B, ∀ L, Active Λ L h z →
      0 ≤ dot L.slope (f z))
    (hceiling : ∀ z ∈ B, Λ.inf' hne (fun L => L.value h z) ≤ M)
    (hstart : Λ.inf' hne (fun L => L.value h (x 0)) = M)
    (hboundary : ∀ z ∈ frontier B,
      Λ.inf' hne (fun L => L.value h z) ≠ M) :
    MapsTo x (Icc 0 T) (interior B) ∧
      ∀ t ∈ Icc 0 T, Λ.inf' hne (fun L => L.value h (x t)) = M := by
  apply Problem326.affineMinimum_trapped Λ hne Label.slope (fun L => L.offset h)
    f B hT hclosed hx hxd hx0
  · intro z hz L hL hactive
    apply hinward z hz L
    exact (active_iff_value_eq_inf hne).2 ⟨hL, hactive⟩
  · exact hceiling
  · exact hstart
  · exact hboundary

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326.BarrierConstruction

/-- Convert the canonical finite-label uniform approximation statement to the
finite-index interface consumed by the network barrier construction. -/
theorem uniformAffineApproximation_of_finite_labels {d : ℕ}
    (hlabels : ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
      ∃ Λ : Finset (Affine.Label d), Λ.Nonempty ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
        ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
          Affine.Cube (-1) 1 p → ∀ L : Affine.Label d,
            Affine.Active Λ L h (Affine.powerPoint h p) →
            ‖p - L.slope‖ < E L.slope) :
    UniformAffineApproximation d := by
  classical
  intro E hE
  obtain ⟨Λ, hΛ, h₀, hh₀, happrox⟩ := hlabels E hE
  let S := {L : Affine.Label d // L ∈ Λ}
  have hS : Nonempty S := by
    obtain ⟨L, hL⟩ := hΛ
    exact ⟨⟨L, hL⟩⟩
  let : Nonempty S := hS
  let e := Fintype.equivFin S
  let r : Fin (Fintype.card S) → Fin d → ℝ := fun j => (e.symm j).val.slope
  let c : Fin (Fintype.card S) → ℝ → ℝ := fun j => (e.symm j).val.offset
  refine ⟨Fintype.card S, Fintype.card_pos, r, c, h₀, hh₀, ?_⟩
  intro h hh hhsmall p hp j hj i
  have hcube : Affine.Cube (-1) 1 p := fun k => abs_le.mp (hp k)
  have ha : Affine.Active Λ (e.symm j).val h (Affine.powerPoint h p) := by
    refine ⟨(e.symm j).property, ?_⟩
    intro J hJ
    have hc := hj (e ⟨J, hJ⟩)
    simpa only [r, c, Affine.Label.value, Affine.powerPoint, dot,
      Equiv.symm_apply_apply] using hc
  have hn := happrox h hh hhsmall p hcube (e.symm j).val ha
  have hc := (pi_norm_lt_iff (hE (e.symm j).val.slope)).mp hn i
  simpa only [r, Pi.sub_apply, Real.norm_eq_abs] using hc

end Problem326.BarrierConstruction

end

end OAI
end
end

section
section
namespace OAI


open Filter Topology

noncomputable section
namespace Problem326

/-- Compactness upgrades a strict sequential activity bound to a uniform
small-parameter bound. No continuity of the activity predicate is needed. -/
theorem uniform_activity_of_sequential_bound
    {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K) (active : ℝ → X → Prop)
    (error : X → ℝ) (herror : Continuous error) (bound : ℝ)
    (hseq : ∀ (h : ℕ → ℝ) (p : ℕ → X) (p₀ : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      p₀ ∈ K → Tendsto p atTop (𝓝 p₀) →
      (∀ n, active (h n) (p n)) → error p₀ < bound) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, active h p → error p < bound := by
  by_contra hnot
  push Not at hnot
  have hwitness : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
      ∃ p ∈ K, active h p ∧ bound ≤ error p := by
    intro n
    exact hnot (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hhpos hhsmall p hpK hpactive hperror using hwitness
  have hhlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hhpos n).le) (fun n => (hhsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p₀, hp₀, φ, hφ, hpφ⟩ := hK.tendsto_subseq hpK
  have hstrict : error p₀ < bound := hseq (h ∘ φ) (p ∘ φ) p₀
    (fun n => hhpos (φ n)) (hhlim.comp hφ.tendsto_atTop) hp₀ hpφ
    (fun n => hpactive (φ n))
  have hweak : bound ≤ error p₀ := ge_of_tendsto'
    ((herror.tendsto p₀).comp hpφ) (fun n => hperror (φ n))
  exact (not_lt_of_ge hweak) hstrict

/-- The uniform activity bound for finitely many labels. The error tolerance
may depend arbitrarily on the label; no regularity in that dependence is used. -/
theorem finite_uniform_activity_of_sequential_bound
    {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]
    {I : Type uI} [Finite I] {K : Set X} (hK : IsCompact K)
    (active : ℝ → X → I → Prop) (error : I → X → ℝ)
    (herror : ∀ i, Continuous (error i)) (bound : I → ℝ)
    (hseq : ∀ (i : I) (h : ℕ → ℝ) (p : ℕ → X) (p₀ : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      p₀ ∈ K → Tendsto p atTop (𝓝 p₀) →
      (∀ n, active (h n) (p n) i) → error i p₀ < bound i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      ∀ p ∈ K, ∀ i, active h p i → error i p < bound i := by
  have hev : ∀ i : I, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ p ∈ K, active h p i → error i p < bound i := by
    intro i
    obtain ⟨δ, hδ, hδprop⟩ := uniform_activity_of_sequential_bound hK
      (fun h p => active h p i) (error i) (herror i) (bound i) (hseq i)
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    exact ⟨δ, hδ, fun h hh => hδprop h hh.1 hh.2⟩
  have hevall := Filter.eventually_all.mpr hev
  obtain ⟨δ, hδ, hδprop⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevall
  refine ⟨δ, hδ, ?_⟩
  intro h hhpos hhsmall p hp i
  exact hδprop ⟨hhpos, hhsmall⟩ i p hp

end Problem326

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace Problem326

open Filter Topology

/-- A continuous scalar function on a compact set stays uniformly away from
any value which it never attains. Empty compact sets are allowed. -/
theorem compact_uniform_gap_of_ne
    {X : Type uX} [TopologicalSpace X] {K : Set X} {f : X → ℝ} {t : ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hne : ∀ x ∈ K, f x ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ |f x - t| := by
  apply hK.exists_forall_le' ((hf.sub continuousOn_const).abs)
  intro x hx
  exact abs_pos.mpr (sub_ne_zero.mpr (hne x hx))

/-- The strict conclusions of finitely many closed active-label conditions
extend from one level of a continuous function to a neighborhood of that level.
Each tolerance is fixed separately; no continuity in the label is required. -/
theorem finite_closed_family_extend_fiber
    {X : Type uX} {ι : Type uIota} [TopologicalSpace X] [Finite ι]
    {K : Set X} (hK : IsCompact K)
    (A : ι → Set X) (hA : ∀ i, IsClosed (A i))
    (μ : X → ℝ) (hμ : Continuous μ)
    (error : ι → X → ℝ) (herror : ∀ i, Continuous (error i))
    (E : ι → ℝ) (t : ℝ)
    (hgood : ∀ i x, x ∈ K → x ∈ A i → μ x = t → error i x < E i) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ i x, x ∈ K → x ∈ A i → |μ x - t| < ρ → error i x < E i := by
  let B : Set X := ⋃ i, K ∩ A i ∩ {x | E i ≤ error i x}
  have hB : IsCompact B := by
    apply isCompact_iUnion
    intro i
    exact (hK.inter_right (hA i)).inter_right (isClosed_le continuous_const (herror i))
  have hne : ∀ x ∈ B, μ x ≠ t := by
    intro x hx heq
    rcases Set.mem_iUnion.mp hx with ⟨i, ⟨hxK, hxA⟩, hxerr⟩
    exact (not_le_of_gt (hgood i x hxK hxA heq)) hxerr
  obtain ⟨ρ, hρ, hgap⟩ := compact_uniform_gap_of_ne hB hμ.continuousOn hne
  refine ⟨ρ, hρ, ?_⟩
  intro i x hxK hxA hxgap
  by_contra h
  have hxB : x ∈ B := Set.mem_iUnion.mpr ⟨i, ⟨hxK, hxA⟩, le_of_not_gt h⟩
  exact (not_lt_of_ge (hgap x hxB)) hxgap

/-- Limit points of active parameters as the positive scale tends to zero.
This neighborhood formulation needs no regularity of the activity predicate. -/
def AsymptoticActive {X : Type uX} [PseudoMetricSpace X]
    (active : ℝ → X → Prop) (p : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h < ε ∧
    ∃ q : X, dist q p < ε ∧ active h q

/-- Diagonal closure of asymptotic activity, without assuming continuity of
any scale-dependent affine offset. -/
theorem isClosed_asymptoticActive {X : Type uX} [PseudoMetricSpace X]
    (active : ℝ → X → Prop) : IsClosed {p | AsymptoticActive active p} := by
  apply IsSeqClosed.isClosed
  intro u p hu hup ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hup (ε / 2) (half_pos hε)
  obtain ⟨h, hh, hhε, q, hqu, hactive⟩ := hu n (ε / 2) (half_pos hε)
  refine ⟨h, hh, lt_trans hhε (half_lt_self hε), q, ?_, hactive⟩
  have hnp := hn n le_rfl
  calc dist q p ≤ dist q (u n) + dist (u n) p := dist_triangle _ _ _
       _ < ε := by linarith

/-- An actual convergent active sequence yields asymptotic activity. -/
theorem asymptoticActive_of_sequences {X : Type uX} [PseudoMetricSpace X]
    (active : ℝ → X → Prop) {h : ℕ → ℝ} {q : ℕ → X} {p : X}
    (hhpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 p)) (hactive : ∀ n, active (h n) (q n)) :
    AsymptoticActive active p := by
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hq ε hε
  have hevent : ∀ᶠ n in atTop, h n < ε := hh.eventually (gt_mem_nhds hε)
  obtain ⟨m, hm⟩ := eventually_atTop.mp hevent
  let k := max n m
  exact ⟨h k, hhpos k, hm k (le_max_right _ _), q k,
    hn k (le_max_left _ _), hactive k⟩

/-- Every asymptotically active point has a realizing sequence. -/
theorem AsymptoticActive.exists_sequences {X : Type uX} [PseudoMetricSpace X]
    {active : ℝ → X → Prop} {p : X} (hp : AsymptoticActive active p) :
    ∃ (h : ℕ → ℝ) (q : ℕ → X),
      (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 p) ∧
      ∀ n, active (h n) (q n) := by
  have hδ : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := by
    intro n
    positivity
  choose h hhpos hhδ q hqδ hactive using fun n => hp _ (hδ n)
  have hδlim : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hhlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => le_of_lt (hhpos n)) (fun n => le_of_lt (hhδ n)) hδlim
  have hqlim : Tendsto q atTop (𝓝 p) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hqδ n)) hδlim
  exact ⟨h, q, hhpos, hhlim, hqlim, hactive⟩

/-- The localization step for arbitrary scale-dependent active families.
Its hypothesis is precisely a strict error bound for every active sequence
whose limit lies in one prescribed level set. -/
theorem active_family_extend_fiber
    {X : Type uX} {ι : Type uIota} [PseudoMetricSpace X] [Finite ι]
    {K : Set X} (hK : IsCompact K)
    (active : ι → ℝ → X → Prop)
    (μ : X → ℝ) (hμ : Continuous μ)
    (error : ι → X → ℝ) (herror : ∀ i, Continuous (error i))
    (E : ι → ℝ) (t : ℝ)
    (hgood : ∀ (i : ι) (h : ℕ → ℝ) (q : ℕ → X) (p : X),
      p ∈ K → μ p = t → (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto q atTop (𝓝 p) → (∀ n, active i (h n) (q n)) → error i p < E i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i p, p ∈ K → |μ p - t| < ρ →
      AsymptoticActive (active i) p → error i p < E i := by
  obtain ⟨ρ, hρ, hlocal⟩ := finite_closed_family_extend_fiber hK
    (fun i => {p | AsymptoticActive (active i) p})
    (fun i => isClosed_asymptoticActive (active i)) μ hμ error herror E t (by
      intro i p hp hactive hlevel
      obtain ⟨h, q, hhpos, hhlim, hqlim, hact⟩ := hactive.exists_sequences
      exact hgood i h q p hp hlevel hhpos hhlim hqlim hact)
  exact ⟨ρ, hρ, fun i p hp hgap hact => hlocal i p hp hact hgap⟩

/-- Compactness turns a strict bound on all limiting active points into a
uniform bound at every sufficiently small positive scale. -/
theorem uniform_activity_of_asymptotic
    {X : Type uX} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    (active : ℝ → X → Prop) (error : X → ℝ) (herror : Continuous error) (E : ℝ)
    (hgood : ∀ p ∈ K, AsymptoticActive active p → error p < E) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∀ p ∈ K, active h p → error p < E := by
  by_contra hfail
  push Not at hfail
  have hw : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < (1 : ℝ) / (n + 1) ∧
      ∃ p ∈ K, active h p ∧ E ≤ error p := by
    intro n
    exact hfail _ (by positivity)
  choose h hhpos hhsmall q hqK hactive hbad using hw
  have hhlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => le_of_lt (hhpos n)) (fun n => le_of_lt (hhsmall n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hpK, φ, hφ, hqφ⟩ := hK.tendsto_subseq hqK
  have hact : AsymptoticActive active p :=
    asymptoticActive_of_sequences active (fun n => hhpos (φ n))
      (hhlim.comp hφ.tendsto_atTop) hqφ (fun n => hactive (φ n))
  have hbadlim : E ≤ error p :=
    ge_of_tendsto (herror.continuousAt.tendsto.comp hqφ)
      (Eventually.of_forall fun n => hbad (φ n))
  exact (not_le_of_gt (hgood p hpK hact)) hbadlim

/-- The scale in the uniform activity estimate can be chosen simultaneously
for finitely many labels. -/
theorem finite_uniform_activity_of_asymptotic
    {X : Type uX} {ι : Type uIota} [PseudoMetricSpace X] [Finite ι]
    {K : Set X} (hK : IsCompact K)
    (active : ι → ℝ → X → Prop) (error : ι → X → ℝ)
    (herror : ∀ i, Continuous (error i)) (E : ι → ℝ)
    (hgood : ∀ i p, p ∈ K → AsymptoticActive (active i) p → error i p < E i) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∀ i p, p ∈ K → active i h p → error i p < E i := by
  choose H hHpos hH using fun i =>
    uniform_activity_of_asymptotic hK (active i) (error i) (herror i) (E i) (hgood i)
  have hHrange : ∀ a ∈ Set.range H, 0 < a := by
    rintro a ⟨i, rfl⟩
    exact hHpos i
  obtain ⟨h0, hh0, hbound⟩ := (Set.finite_range H).isCompact.exists_forall_le'
    continuous_id.continuousOn hHrange
  refine ⟨h0, hh0, ?_⟩
  intro h hhpos hhsmall i p hp hact
  exact hH i h hhpos (lt_of_lt_of_le hhsmall (hbound _ ⟨i, rfl⟩)) p hp hact

end Problem326

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter Topology

namespace Problem326.Affine

/-- A fixed full affine certificate gives a uniform activity bound on its
exponent cube at all sufficiently small positive scales. -/
theorem FullCertificate.uniform_activity {d : ℕ} {a b : ℝ}
    {E : (Fin d → ℝ) → ℝ} (C : FullCertificate d a b E) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 →
      ∀ p : Fin d → ℝ, Cube a b p → ∀ L ∈ C.labels,
        Active C.labels L h (powerPoint h p) → ‖p - L.slope‖ < E L.slope := by
  classical
  let ι := {L : Label d // L ∈ C.labels}
  let active : ι → ℝ → (Fin d → ℝ) → Prop :=
    fun L h p => Active C.labels L.val h (powerPoint h p)
  obtain ⟨h0, hh0, huniform⟩ := Problem326.finite_uniform_activity_of_asymptotic
    (K := Set.Icc (fun _ : Fin d => a) (fun _ => b)) isCompact_Icc
    active (fun L p => ‖p - L.val.slope‖)
    (fun _ => (continuous_id.sub continuous_const).norm)
    (fun L => E L.val.slope) (by
      intro L p hp hact
      obtain ⟨h, q, hhpos, hhlim, hqlim, hactive⟩ := hact.exists_sequences
      exact C.approximation L.val L.property h q p hhpos hhlim hqlim
        (fun i => ⟨hp.1 i, hp.2 i⟩) hactive)
  refine ⟨h0, hh0, ?_⟩
  intro h hhpos hhsmall p hp L hL hact
  exact huniform h hhpos hhsmall ⟨L, hL⟩ p
    ⟨fun i => (hp i).1, fun i => (hp i).2⟩ hact

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326.Affine

/-- Reindex the fixed finite label set by `Fin n`, as required by the
network barrier construction. This theorem is definitionally the uniform
approximation interface there, with the active comparison expanded. -/
theorem FullCertificate.uniform_affine_data {d : ℕ}
    {E : (Fin d → ℝ) → ℝ} (hE : ∀ r, 0 < E r)
    (C : FullCertificate d (-1) 1 E) :
    ∃ n : ℕ, 0 < n ∧ ∃ (r : Fin n → Fin d → ℝ)
      (c : Fin n → ℝ → ℝ) (h₀ : ℝ), 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
        (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
          (∀ k : Fin n,
            dot (r j) (fun i => h ^ p i) + c j h ≤
              dot (r k) (fun i => h ^ p i) + c k h) →
          ∀ i, |p i - r j i| < E (r j) := by
  classical
  let ι := {L : Label d // L ∈ C.labels}
  let : Nonempty ι := ⟨⟨C.nonempty.choose, C.nonempty.choose_spec⟩⟩
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let r : Fin (Fintype.card ι) → Fin d → ℝ := fun j => (e.symm j).val.slope
  let c : Fin (Fintype.card ι) → ℝ → ℝ := fun j => (e.symm j).val.offset
  obtain ⟨h₀, hh₀, huniform⟩ := C.uniform_activity
  refine ⟨Fintype.card ι, Fintype.card_pos, r, c, h₀, hh₀, ?_⟩
  intro h hhpos hhsmall p hp j ha i
  have hpcube : Cube (-1) 1 p := fun k => abs_le.mp (hp k)
  have hactive : Active C.labels (e.symm j).val h (powerPoint h p) := by
    refine ⟨(e.symm j).property, ?_⟩
    intro J hJ
    have hc := ha (e ⟨J, hJ⟩)
    simpa [r, c, Label.value, dot, powerPoint] using hc
  have hnorm := huniform h hhpos hhsmall p hpcube (e.symm j).val
    (e.symm j).property hactive
  have hi := (pi_norm_lt_iff (hE ((e.symm j).val.slope))).mp hnorm i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi

/-- The full affine-certificate theorem supplies the network's entire
arbitrary-positive-tolerance uniform approximation interface. -/
theorem uniform_affine_data_of_full_certificates {d : ℕ}
    (hfull : ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
      Nonempty (FullCertificate d (-1) 1 E)) :
    ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
      ∃ n : ℕ, 0 < n ∧ ∃ (r : Fin n → Fin d → ℝ)
        (c : Fin n → ℝ → ℝ) (h₀ : ℝ), 0 < h₀ ∧
        ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
          (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
            (∀ k : Fin n,
              dot (r j) (fun i => h ^ p i) + c j h ≤
                dot (r k) (fun i => h ^ p i) + c k h) →
            ∀ i, |p i - r j i| < E (r j) := by
  intro E hE
  obtain ⟨C⟩ := hfull E hE
  exact C.uniform_affine_data hE

end Problem326.Affine

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace Problem326

theorem compact_convex_invariant_polytope :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ K : Set (Fin d → ℝ),
        IsCompact K ∧ Convex ℝ K ∧ IsFinitePolyhedron K ∧
        x0 ∈ K ∧ K ⊆ {x | PositiveState x} ∧ IsForwardInvariant N κ K := by
  intro d N κ _ hweak hκ x0 hx0
  apply BarrierConstruction.compact_convex_invariant_polytope_of_uniform ?_
    N κ hweak hκ x0 hx0
  exact Affine.uniform_affine_data_of_full_certificates
    (fun E hE => Affine.exists_fullCertificate d (-1) 1 E (by norm_num)
      (fun r _ => hE r))

theorem global_bounded_persistent_solution_oai :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
        ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  intro d N κ hd hweak hκ x0 hx0
  obtain ⟨K, hK, _, _, hxK, hpos, hinv⟩ :=
    compact_convex_invariant_polytope d N κ hd hweak hκ x0 hx0
  exact global_bounds_of_compact_invariant N κ x0 hK hxK hpos hinv

end Problem326

end

end OAI
end
end

theorem solution : type_of% @OAI.Problem326.global_bounded_persistent_solution_oai := @OAI.Problem326.global_bounded_persistent_solution_oai
