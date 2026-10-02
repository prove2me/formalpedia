-- Prove2me | solution 7 for MilnorDynamics.not_locally_bounded_subseq_diverges
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T08:27:57.725522+00:00
-- url     : https://prove2.me/submissions/95b63e89-63ac-459f-beb2-7fc670029fbe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_subseq_escapes_on_compacts
import Theorems.Thm_MilnorDynamics_escapes_on_compacts_implies_diverges

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- The exhaustion sets: a compact ball intersected with the complement of a thickening
of the complement of `U`. -/
noncomputable def escK (U : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) (n : ℝ) ∩ (Metric.thickening ((1 : ℝ) / (n + 1)) (Uᶜ))ᶜ

lemma escK_subset (U : Set ℂ) (n : ℕ) : escK U n ⊆ U := by
  intro z hz
  by_contra hzU
  have hδ : (0 : ℝ) < (1 : ℝ) / (n + 1) := by positivity
  exact hz.2 (Metric.self_subset_thickening hδ (Uᶜ) hzU)

lemma escK_compact (U : Set ℂ) (n : ℕ) : IsCompact (escK U n) := by
  have hball : IsCompact (Metric.closedBall (0 : ℂ) (n : ℝ)) :=
    isCompact_closedBall (0 : ℂ) (n : ℝ)
  have hclosed : IsClosed (escK U n) := by
    show IsClosed (Metric.closedBall (0 : ℂ) (n : ℝ) ∩
      (Metric.thickening ((1 : ℝ) / (n + 1)) (Uᶜ))ᶜ)
    exact hball.isClosed.inter Metric.isOpen_thickening.isClosed_compl
  exact IsCompact.of_isClosed_subset hball hclosed Set.inter_subset_left

lemma escK_mono (U : Set ℂ) {m n : ℕ} (h : m ≤ n) : escK U m ⊆ escK U n := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall] at hz1 ⊢
    exact le_trans hz1 (by exact_mod_cast h)
  · intro hzn
    refine hz2 (Metric.thickening_mono ?_ (Uᶜ) hzn)
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      linarith
    exact one_div_le_one_div_of_le hm hle

/-- Every point of `U` lies in some level of the exhaustion. -/
lemma escK_cover (U : Set ℂ) (hU : IsOpen U) : ∀ z ∈ U, ∃ n, z ∈ escK U n := by
  intro z hzU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ (1 / ε))
  have hzn : ‖z‖ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have h1 : 1 / ε < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ε) h1.le
  have hεn : (1 : ℝ) / (n + 1) ≤ ε := by
    have h2 : (1 : ℝ) / (n : ℝ) < ε := by
      rw [div_lt_iff₀ hnpos]
      rw [div_lt_iff₀ hε] at h1
      nlinarith
    have h3 : (1 : ℝ) / (n + 1) ≤ 1 / (n : ℝ) := by
      apply one_div_le_one_div_of_le hnpos
      linarith
    linarith
  have hznot : z ∉ Metric.thickening ε (Uᶜ) := by
    intro hmem
    obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.mp hmem
    exact hy (hball (by simpa [Metric.mem_ball, dist_comm] using hzy))
  refine ⟨n, ?_, ?_⟩
  · rw [Metric.mem_closedBall]
    simpa [dist_eq_norm] using hzn.le
  · intro hmem
    exact hznot (Metric.thickening_mono hεn (Uᶜ) hmem)

/-- Every point of `U` has a ball around it contained in one of the `escK U j`. -/
lemma escK_ball_subset (U : Set ℂ) (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) :
    ∃ (j : ℕ) (r : ℝ), 0 < r ∧ Metric.ball z r ⊆ escK U j := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  obtain ⟨j, hj⟩ := exists_nat_gt (max (‖z‖ + ε / 2) (2 / ε))
  have hzj : ‖z‖ + ε / 2 < (j : ℝ) := lt_of_le_of_lt (le_max_left _ _) hj
  have h2j : 2 / ε < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
  have hεj : (1 : ℝ) / (j + 1) ≤ ε / 2 := by
    have hjpos : (0 : ℝ) < (j : ℝ) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / ε) h2j.le
    have h1 : (1 : ℝ) / (j : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hjpos]
      rw [div_lt_iff₀ hε] at h2j
      nlinarith
    have h2 : (1 : ℝ) / (j + 1) ≤ 1 / (j : ℝ) := by
      apply one_div_le_one_div_of_le hjpos
      linarith
    linarith
  refine ⟨j, ε / 2, by positivity, ?_⟩
  intro w hw
  have hwz : dist w z < ε / 2 := by simpa [Metric.mem_ball] using hw
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall]
    have h1 : dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
    have h2 : dist z 0 = ‖z‖ := by simp [dist_eq_norm]
    linarith
  · intro hwt
    obtain ⟨y, hy, hwy⟩ := Metric.mem_thickening_iff.mp hwt
    have hzy : dist z y < ε := by
      have h1 : dist z y ≤ dist z w + dist w y := dist_triangle z w y
      have h2 : dist z w < ε / 2 := by simpa [dist_comm] using hwz
      have h3 : dist w y < ε / 2 := lt_of_lt_of_le hwy hεj
      linarith
    exact hy (hball (by simpa [Metric.mem_ball, dist_comm] using hzy))

/-- A compact set is contained in one level of the exhaustion. -/
lemma exists_escK_superset (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ j : ℕ, K ⊆ escK U j := by
  classical
  have hpt : ∀ z : ↥K, ∃ (j : ℕ) (r : ℝ), 0 < r ∧ Metric.ball (z : ℂ) r ⊆ escK U j :=
    fun z => escK_ball_subset U hU (hKU z.2)
  choose jz rz hrz hsub using hpt
  have hcover : K ⊆ ⋃ z : ↥K, Metric.ball (z : ℂ) (rz z) := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, by simpa using hrz ⟨w, hw⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : ↥K => Metric.ball (z : ℂ) (rz z))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t.sup jz, ?_⟩
  intro w hw
  have hwt := ht hw
  simp only [mem_iUnion, exists_prop] at hwt
  obtain ⟨z, hzt, hzw⟩ := hwt
  exact escK_mono U (Finset.le_sup (f := jz) hzt) (hsub z hzw)

theorem localEscape (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧ ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f (φ n) z‖ := by
  classical
  -- a fixed point of `U`, and an exhaustion level containing it
  obtain ⟨z₀, hz₀U⟩ := hUc.nonempty
  obtain ⟨n₀, hn₀⟩ := escK_cover U hU z₀ hz₀U
  let K : ℕ → Set ℂ := fun j => escK U (n₀ + j)
  have hKsub : ∀ j, K j ⊆ U := fun j => escK_subset U (n₀ + j)
  have hKcom : ∀ j, IsCompact (K j) := fun j => escK_compact U (n₀ + j)
  have hKne : ∀ j, z₀ ∈ K j := fun j => escK_mono U (Nat.le_add_right n₀ j) hn₀
  -- one recursion step: an extraction on `K j` yields one on `K (j+1)`
  have step_ex : ∀ (j : ℕ) (θ : ℕ → ℕ), StrictMono θ →
      (∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K j, R < ‖f (θ n) z‖) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K (j + 1), R < ‖f ((θ ∘ ψ) n) z‖ := by
    intro j θ _ hθe
    have hsub : ∀ n, DifferentiableOn ℂ (f (θ n)) U ∧
        MapsTo (f (θ n)) U ({0, 1}ᶜ : Set ℂ) := fun n => hf (θ n)
    have hsubbdd : ∃ K' ⊆ U, IsCompact K' ∧
        ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K', ‖f (θ n) z‖ ≤ M) := by
      refine ⟨K j, hKsub j, hKcom j, ?_⟩
      rintro ⟨M, hM⟩
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hθe (M + 1))
      have hlt : M + 1 < ‖f (θ N) z₀‖ := hN N le_rfl z₀ (hKne j)
      have hle : ‖f (θ N) z₀‖ ≤ M := hM N z₀ (hKne j)
      linarith
    exact exists_subseq_escapes_on_compacts U hU hUc (fun n => f (θ n)) hsub hsubbdd
      (K (j + 1)) (hKsub (j + 1)) (hKcom (j + 1))
  -- the chain of nested extractions, carried as a subtype
  let P : ℕ → Type := fun j =>
    {θ : ℕ → ℕ // StrictMono θ ∧ ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K j, R < ‖f (θ n) z‖}
  let base : P 0 :=
    ⟨(Classical.choose (exists_subseq_escapes_on_compacts U hU hUc f hf hbdd
        (K 0) (hKsub 0) (hKcom 0))),
     (Classical.choose_spec (exists_subseq_escapes_on_compacts U hU hUc f hf hbdd
        (K 0) (hKsub 0) (hKcom 0))).1,
     (Classical.choose_spec (exists_subseq_escapes_on_compacts U hU hUc f hf hbdd
        (K 0) (hKsub 0) (hKcom 0))).2⟩
  let psi : ∀ j, P j → ℕ → ℕ := fun j ih => Classical.choose (step_ex j ih.1 ih.2.1 ih.2.2)
  have psi_mono : ∀ j (ih : P j), StrictMono (psi j ih) :=
    fun j ih => (Classical.choose_spec (step_ex j ih.1 ih.2.1 ih.2.2)).1
  have psi_esc : ∀ j (ih : P j), ∀ R : ℝ, ∀ᶠ n in atTop,
      ∀ z ∈ K (j + 1), R < ‖f ((ih.1 ∘ psi j ih) n) z‖ :=
    fun j ih => (Classical.choose_spec (step_ex j ih.1 ih.2.1 ih.2.2)).2
  let step : ∀ j, P j → P (j + 1) := fun j ih =>
    ⟨ih.1 ∘ psi j ih, ih.2.1.comp (psi_mono j ih), psi_esc j ih⟩
  let Gd : ∀ j, P j := fun j => Nat.rec (motive := P) base step j
  have hGd : ∀ j, (Gd (j + 1)).1 = (Gd j).1 ∘ psi j (Gd j) := fun j => rfl
  -- later extractions are subsequences of earlier ones
  have hnest : ∀ (j : ℕ) ⦃j' : ℕ⦄, j ≤ j' → ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ (Gd j').1 = (Gd j).1 ∘ σ := by
    intro j j' h
    induction j', h using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, by simp [Function.comp_def]⟩
    | succ k _ ih =>
        obtain ⟨σ, hσm, hσe⟩ := ih
        refine ⟨σ ∘ psi k (Gd k), hσm.comp (psi_mono k (Gd k)), ?_⟩
        rw [hGd k, hσe, Function.comp_assoc]
  -- the diagonal
  let φ : ℕ → ℕ := fun n => (Gd n).1 n
  have hφmono : StrictMono φ := by
    intro a b hab
    obtain ⟨σ, hσm, hσe⟩ := hnest a (le_of_lt hab)
    have hlt : a < σ b := lt_of_lt_of_le hab (StrictMono.id_le hσm b)
    have hb : φ b = (Gd a).1 (σ b) := by simp only [φ, hσe, Function.comp_apply]
    have ha : φ a = (Gd a).1 a := rfl
    rw [hb, ha]
    exact (Gd a).2.1 hlt
  have hφesc : ∀ K' ⊆ U, IsCompact K' → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K', R < ‖f (φ n) z‖ := by
    intro K' hK'U hK' R
    obtain ⟨j, hj⟩ := exists_escK_superset U hU K' hK'U hK'
    obtain ⟨m, hm⟩ := exists_nat_gt (max (j : ℝ) R)
    have hjm : j ≤ m := by exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_left _ _) hm)
    have hRm : R ≤ (m : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hm)
    have hK'm : K' ⊆ K m := fun z hz => escK_mono U (by omega) (hj hz)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Gd m).2.2 (m : ℝ))
    refine eventually_atTop.mpr ⟨max m N, ?_⟩
    intro n hn
    have hmn : m ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨σ, hσm, hσe⟩ := hnest m hmn
    have hidx : n ≤ σ n := StrictMono.id_le hσm n
    have hNn : N ≤ σ n := le_trans (le_trans (le_max_right _ _) hn) hidx
    have hval : φ n = (Gd m).1 (σ n) := by
      simp only [φ, hσe, Function.comp_apply]
    rw [hval]
    intro z hz
    have hzK : z ∈ K m := hK'm hz
    have h1 : (m : ℝ) < ‖f ((Gd m).1 (σ n)) z‖ := hN (σ n) hNn z hzK
    linarith
  exact ⟨φ, hφmono, hφesc⟩

theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      DivergesLocallyUniformlyFrom (fun n => f (φ n)) U ({0, 1}ᶜ : Set ℂ) := by
  -- `localEscape` already returns the escape statement *about its own*
  -- subsequence: `hesc : forall K, IsCompact K -> forall R, eventually
  -- ... f (phiLocal n) z`.  So the family whose escape has been established is
  -- `fun n => f (phiLocal n)`, and `escapes_on_compacts_implies_diverges` must
  -- be applied to that family, not to the original `f`.
  --
  -- An earlier revision instead applied the helper to `fun n => f (phi n)`
  -- (the goal's own binder) while still passing `hesc` and `hf` unchanged.
  -- That double-counted the subsequence and elaborated the escape claim as
  -- `f (phi (phi n)) z` where `f (phi n) z` was required.
  obtain ⟨phiLocal, hPhiLocal, hesc⟩ := localEscape U hU hUc f hf hbdd
  refine ⟨phiLocal, hPhiLocal, ?_⟩
  apply escapes_on_compacts_implies_diverges U hU (fun n => f (phiLocal n))
  · intro n
    exact hf (phiLocal n)
  · intro K hKU hK R
    -- `hesc` is already stated for the family `fun n => f (phiLocal n)`, so it
    -- is used directly with no reindexing.
    exact hesc K hKU hK R
