-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:41.888961+00:00
-- url     : https://prove2.me/submissions/5048f2e0-22c9-436f-a419-30ac05b200ce

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
section
@[expose] public section
universe u
open MeasureTheory Set Filter Topology
private lemma isCompact_bnd (N : ℕ → ℕ) : IsCompact (Bnd N) := by
  have : Bnd N = Set.pi Set.univ (fun i => Set.Iic (N i)) := by
    ext g
    simp only [Bnd, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  rw [this]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (N i)).isCompact
private lemma bnd_subset_cyl (N : ℕ → ℕ) (n : ℕ) : Bnd N ⊆ Cyl N n :=
  fun _ hg i _ => hg i
private lemma cyl_succ_eq (N : ℕ → ℕ) (n : ℕ) :
    Cyl N n = ⋃ k : ℕ, (Cyl N n ∩ {g | g (n + 1) ≤ k}) := by
  ext g; simp only [Cyl, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun h => ⟨g (n + 1), h, le_refl _⟩, fun ⟨_, h, _⟩ => h⟩
private lemma monotone_cyl_split (N : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k}) := by
  intro a b hab x ⟨hx1, hx2⟩
  exact ⟨hx1, le_trans hx2 hab⟩
private lemma cyl_inter_eq_cyl_update (N : ℕ → ℕ) (n k : ℕ) :
    Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k} = Cyl (Function.update N (n + 1) k) (n + 1) := by
  ext g
  simp only [Cyl, Set.mem_inter_iff, Set.mem_ofPred_eq, Function.update]
  constructor
  · rintro ⟨hg, hgk⟩ i hi
    by_cases heq : i = n + 1
    · subst heq; simp [hgk]
    · have : i ≤ n := by omega
      simp [heq, hg i this]
  · intro hg; constructor
    · intro i hi
      specialize hg i (by omega)
      have hi_ne : i ≠ n + 1 := by omega
      simpa [hi_ne] using hg
    · specialize hg (n + 1) (le_refl _)
      simpa using hg
private lemma cyl_ext (N N' : ℕ → ℕ) (n : ℕ) (h : ∀ i, i ≤ n → N i = N' i) :
    Cyl N n = Cyl N' n := by
  ext g; simp_all
private lemma truncate_mem_bnd (N : ℕ → ℕ) (g : ℕ → ℕ) : truncate N g ∈ Bnd N :=
  fun _ => min_le_right _ _
private lemma truncate_agree_on_cyl (N : ℕ → ℕ) (n : ℕ) (g : ℕ → ℕ) (hg : g ∈ Cyl N n) :
    ∀ i, i ≤ n → truncate N g i = g i := by
  intro i hi
  simp only [truncate, min_eq_left (hg i hi)]
private lemma iInter_closure_image_cyl_eq
    {α : Type*} [TopologicalSpace α] [PolishSpace α]
    {f : (ℕ → ℕ) → α} (hf : Continuous f) (N : ℕ → ℕ) :
    ⋂ n, closure (f '' Cyl N n) = f '' Bnd N := by
  have : T2Space α := inferInstance
  apply Set.Subset.antisymm
  · -- Hard direction: ⋂ closure(f '' Cyl N n) ⊆ f '' Bnd N
    -- Use metrizable structure for sequential arguments
    let := TopologicalSpace.upgradeIsCompletelyMetrizable α
    intro y hy
    simp only [Set.mem_iInter] at hy
    -- For each n, y ∈ closure(f '' Cyl N n), so pick z_n ∈ f '' Cyl N n close to y
    have : ∀ n, ∃ g ∈ Cyl N n, dist (f g) y < 1 / (↑n + 1) := by
      intro n
      have : y ∈ closure (f '' Cyl N n) := hy n
      rw [Metric.mem_closure_iff] at this
      obtain ⟨z, hz, hd⟩ := this (1 / (↑n + 1)) (by positivity)
      obtain ⟨g, hg, hfg⟩ := hz
      exact ⟨g, hg, by rw [hfg, dist_comm]; exact hd⟩
    choose g hg_cyl hg_dist using this
    -- Truncate: g'_n = truncate N (g n) ∈ Bnd N
    let g' : ℕ → (ℕ → ℕ) := fun n => truncate N (g n)
    have hg'_bnd : ∀ n, g' n ∈ Bnd N := fun n => truncate_mem_bnd N (g n)
    -- g' n agrees with g n on coordinates ≤ n
    have hg'_agree : ∀ n i, i ≤ n → g' n i = g n i :=
      fun n => truncate_agree_on_cyl N n (g n) (hg_cyl n)
    -- By compactness of Bnd N, g' has a convergent subsequence
    have hBnd_compact := isCompact_bnd N
    have hBnd_seq := hBnd_compact.isSeqCompact
    obtain ⟨g_star, hg_star_bnd, φ, hφ_strict, hg'_conv⟩ :=
      hBnd_seq (fun n => hg'_bnd n)
    -- g(φ n) also converges to g_star in ℕ → ℕ
    -- Because g' (φ n) and g (φ n) agree on coordinates ≤ φ n, and φ n → ∞
    have hg_conv : Tendsto (fun n => g (φ n)) atTop (𝓝 g_star) := by
      rw [tendsto_pi_nhds]
      intro i
      simp only [nhds_discrete, Filter.tendsto_pure]
      have hg'_ev : ∀ᶠ n in atTop, g' (φ n) i = g_star i := by
        rw [tendsto_pi_nhds] at hg'_conv
        simp_all
      have hφ_ev : ∀ᶠ n in atTop, i ≤ φ n :=
        (hφ_strict.tendsto_atTop).eventually (Filter.eventually_ge_atTop i)
      filter_upwards [hg'_ev, hφ_ev] with n h1 h2
      rw [← h1, hg'_agree (φ n) i h2]
    -- f(g(φ n)) → f(g_star) by continuity
    have hf_conv : Tendsto (fun n => f (g (φ n))) atTop (𝓝 (f g_star)) :=
      hf.continuousAt.tendsto.comp hg_conv
    -- f(g(φ n)) → y by the distance bound
    have hfy : Tendsto (fun n => f (g (φ n))) atTop (𝓝 y) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have h1div : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hφ_top := hφ_strict.tendsto_atTop
      have h_comp : Tendsto (fun n => (1 : ℝ) / (↑(φ n) + 1)) atTop (𝓝 0) :=
        h1div.comp hφ_top
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp h_comp) ε hε
      use M
      intro n hn
      have hdist_bound := hg_dist (φ n)
      have hsmall : (1 : ℝ) / (↑(φ n) + 1) < ε := by
        have h := hM n hn
        rwa [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at h
      exact lt_trans hdist_bound hsmall
    -- By uniqueness of limits in T2: f(g_star) = y
    have : f g_star = y := tendsto_nhds_unique hf_conv hfy
    exact ⟨g_star, hg_star_bnd, this⟩
  · -- Easy direction: f '' Bnd N ⊆ ⋂ closure(f '' Cyl N n)
    intro y hy
    simp only [Set.mem_iInter]
    intro n
    apply subset_closure
    obtain ⟨g, hg, hfg⟩ := hy
    exact ⟨g, bnd_subset_cyl N n hg, hfg⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {α : Type*}
    [TopologicalSpace α] [PolishSpace α]
    {cap : Set α → ENNReal}
    (hcap : MeasureTheory.IsChoquetCapacity cap)
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    cap s = ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), cap K := by
  apply le_antisymm
  · -- Hard direction: cap s ≤ ⨆ K compact K⊆s, cap K
    rw [AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf_cont, hf_range⟩
    · exact le_iSup_of_le ∅ (le_iSup_of_le isCompact_empty
        (le_iSup_of_le (Set.empty_subset _) le_rfl))
    · subst hf_range
      apply le_of_forall_lt_imp_le_of_dense
      intro t ht
      -- Write range f = ⋃ k, f '' {g | g 0 ≤ k} (monotone in k)
      have hrange_union : range f = ⋃ k, f '' {g : ℕ → ℕ | g 0 ≤ k} := by
        rw [← Set.image_univ,
          show (Set.univ : Set (ℕ → ℕ)) = ⋃ k, {g : ℕ → ℕ | g 0 ≤ k} from by
            ext g
            simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
            exact ⟨g 0, le_refl _⟩,
          Set.image_iUnion]
      have hmono_base : Monotone (fun k => f '' {g : ℕ → ℕ | g 0 ≤ k}) := by
        intro a b hab; apply Set.image_mono; intro x (hx : x 0 ≤ a); exact le_trans hx hab
      rw [hrange_union, hcap.iUnion_nat _ hmono_base] at ht
      obtain ⟨k₀, hk₀⟩ := lt_iSup_iff.mp ht
      -- Rewrite the base set as a cylinder
      have hcyl0 : f '' {g : ℕ → ℕ | g 0 ≤ k₀} = f '' Cyl (fun _ => k₀) 0 := by
        congr 1; ext g; simp [Cyl]
      -- Recursive step: from cylinder at level n, find bound for level n+1
      have rec_step : ∀ (M : ℕ → ℕ) (n : ℕ), t < cap (f '' Cyl M n) →
          ∃ k, t < cap (f '' Cyl (Function.update M (n + 1) k) (n + 1)) := by
        intro M n hlt_M
        have hsplit : cap (f '' Cyl M n) =
            ⨆ k, cap (f '' (Cyl M n ∩ {g | g (n + 1) ≤ k})) := by
          conv_lhs => rw [cyl_succ_eq M n, Set.image_iUnion]
          exact hcap.iUnion_nat _
            (fun a b h => Set.image_mono (monotone_cyl_split M n h))
        rw [hsplit] at hlt_M
        obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt_M
        exact ⟨k, by rwa [cyl_inter_eq_cyl_update] at hk⟩
      -- Build N_seq : ℕ → (ℕ → ℕ) by Nat.rec
      let build : (n : ℕ) → { M : ℕ → ℕ // t < cap (f '' Cyl M n) } :=
        fun n => Nat.rec
          ⟨fun _ => k₀, hcyl0 ▸ hk₀⟩
          (fun m ⟨M_prev, hM_prev⟩ =>
            ⟨Function.update M_prev (m + 1)
              (Classical.choose (rec_step M_prev m hM_prev)),
             Classical.choose_spec (rec_step M_prev m hM_prev)⟩)
          n
      let N_seq : ℕ → (ℕ → ℕ) := fun n => (build n).val
      have hN_seq_prop : ∀ n, t < cap (f '' Cyl (N_seq n) n) :=
        fun n => (build n).property
      -- Consistency: N_seq (n+1) agrees with N_seq n on coordinates ≤ n
      have hN_seq_consistent : ∀ n i, i ≤ n → N_seq (n + 1) i = N_seq n i := by
        intro n i hi
        change (Function.update (N_seq n) (n + 1) _) i = N_seq n i
        exact Function.update_of_ne (by omega) ..
      -- Define N as the diagonal: N i = N_seq i i
      let N : ℕ → ℕ := fun i => N_seq i i
      -- N agrees with N_seq n on coordinates ≤ n
      have hN_agree : ∀ n i, i ≤ n → N i = N_seq n i := by
        intro n
        induction n with
        | zero => intro i hi; simp only [Nat.le_zero] at hi; subst hi; rfl
        | succ m ih =>
          intro i hi
          by_cases heq : i = m + 1
          · subst heq; rfl
          · have him : i ≤ m := by omega
            simp_all
      -- Cyl N n = Cyl (N_seq n) n
      have hcyl_eq : ∀ n, Cyl N n = Cyl (N_seq n) n :=
        fun n => cyl_ext N (N_seq n) n (hN_agree n)
      -- t < cap(f '' Cyl N n) for all n
      have hcap_bound : ∀ n, t < cap (f '' Cyl N n) :=
        fun n => hcyl_eq n ▸ hN_seq_prop n
      -- Closures: E n = closure(f '' Cyl N n) are antitone closed sets with cap ≥ t
      set E := fun n => closure (f '' Cyl N n) with hE_def
      have hE_closed : ∀ n, IsClosed (E n) := fun _ => isClosed_closure
      have hE_anti : Antitone E := by
        intro m n hmn
        apply closure_mono
        apply Set.image_mono
        intro x (hx : ∀ i, i ≤ n → x i ≤ N i) i hi
        exact hx i (le_trans hi hmn)
      have hE_cap : ∀ n, t < cap (E n) := by
        intro n
        exact lt_of_lt_of_le (hcap_bound n) (hcap.mono subset_closure)
      -- By iInter_closed: cap(⋂ E n) = ⨅ cap(E n) ≥ t
      have hE_inter_cap : cap (⋂ n, E n) = ⨅ n, cap (E n) :=
        hcap.iInter_closed E hE_anti hE_closed
      have ht_le : t ≤ cap (⋂ n, E n) := by
        rw [hE_inter_cap]; exact le_iInf fun n => le_of_lt (hE_cap n)
      -- Key: ⋂ E n = f '' Bnd N (by iInter_closure_image_cyl_eq)
      have hkey : ⋂ n, E n = f '' Bnd N :=
        iInter_closure_image_cyl_eq hf_cont N
      -- f '' Bnd N is compact and ⊆ range f
      have hK_compact : IsCompact (f '' Bnd N) := (isCompact_bnd N).image hf_cont
      have hK_sub : f '' Bnd N ⊆ range f := Set.image_subset_range f _
      -- Conclude
      calc t ≤ cap (⋂ n, E n) := ht_le
        _ = cap (f '' Bnd N) := by rw [hkey]
        _ ≤ ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ range f), cap K :=
            le_iSup_of_le _ (le_iSup_of_le hK_compact (le_iSup_of_le hK_sub le_rfl))
  · -- Easy direction
    exact iSup_le fun K => iSup_le fun _ => iSup_le fun hKs => hcap.mono hKs
end MeasureTheory.AnalyticSet
