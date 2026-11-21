-- Prove2me | solution 2 for MasulloGRH.strongDual_nuclear_of_complete_nuclear_DF
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:57:15.36741+00:00
-- url     : https://prove2.me/submissions/7b972c5a-b4d3-4d01-a5b2-a209b067f612

import Theorems.Thm_MasulloGRH_nuclear_banach_map_representation
import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
import Theorems.Thm_MasulloGRH_strongDual_seminorm_of_bounded
import Theorems.Thm_MasulloGRH_strongDual_isHLCS

import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
import Theorems.Thm_MasulloGRH_quasinuclear_domination_of_abs_summing

open MasulloGRH Function Set Bornology Filter Topology
open scoped Pointwise ENNReal

-- A continuous map from a nuclear space into ℓ¹ has absolutely summable
-- coordinate functionals for every seminorm of the strong dual.
private theorem coordinates_abs_summable {G I : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hN : IsNuclear G) (T : G →L[ℂ] lp (fun _ : I => ℂ) 1)
    (p : Seminorm ℂ (StrongDual ℂ G)) (hp : Continuous p) :
    Summable (fun i => p ((lp.evalCLM ℂ (fun _ : I => ℂ) 1 i).comp T)) := by
  obtain ⟨B,C,hB,hC,hpB⟩ := strongDual_seminorm_le_polar G hN.1 p hp
  obtain ⟨q,φ,v,c,hq,hφ,hv,hc,hex⟩ := nuclear_banach_map_representation G _ hN T
  obtain ⟨ι,_,P,hP⟩ := hN.1.1
  let := hP.topologicalAddGroup
  let := hP.continuousSMul
  let := hP.toPolynormableSpace
  obtain ⟨M,hM,hMB⟩ :=
    ((PolynormableSpace.withSeminorms ℂ G).isVonNBounded_iff_seminorm_bounded.mp hB) ⟨q,hq⟩
  let a (z : ℕ × I) : ℝ := ‖c z.1‖ * ‖v z.1 z.2‖
  have ha0 (z : ℕ × I) : 0 ≤ a z := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrow (n : ℕ) : HasSum (fun i => a (n,i)) (‖c n‖ * ‖v n‖) := by
    have h := lp.hasSum_norm (p := 1) (by norm_num) (v n)
    simpa [a] using h.mul_left ‖c n‖
  have ha : Summable a := (summable_prod_of_nonneg ha0).mpr ⟨fun n => (hrow n).summable,by
    change Summable (fun n => ∑' i, a (n,i))
    simp_rw [(hrow _).tsum_eq]
    exact Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => by simpa using mul_le_mul_of_nonneg_left (hv n) (norm_nonneg (c n))) hc⟩
  have hscol (i : I) : Summable (fun n => a (n,i)) := ha.prod_symm.prod_factor i
  have hs : Summable (fun i => ∑' n, a (n,i)) := ha.prod_symm.prod
  refine Summable.of_nonneg_of_le (fun _ => apply_nonneg p _) (fun i => ?_) (hs.mul_left (C * M))
  rw [mul_assoc]
  apply hpB _ _ (mul_nonneg hM.le (tsum_nonneg fun n => ha0 (n,i)))
  intro x hx
  have hi := (lp.evalCLM ℂ (fun _ : I => ℂ) 1 i).hasSum (hex x)
  apply hi.norm_le_of_bounded ((hscol i).hasSum.mul_left M)
  intro n
  change ‖(c n * φ n x) • (v n i)‖ ≤ M * a (n,i)
  rw [norm_smul,norm_mul]
  have h := mul_le_mul_of_nonneg_left ((hφ n x).trans (hMB x hx).le) (norm_nonneg (c n))
  calc
    _ ≤ (‖c n‖ * M) * ‖v n i‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by dsimp [a]; ring

private def AbsSummingBound {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (p q : Seminorm ℂ F) : Prop :=
  ∀ (n : ℕ) (z : Fin n → F) (c : ℝ), (∀ f : StrongDual ℂ F,
    (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (z i)‖ ≤ c) → ∑ i, p (z i) ≤ c

private theorem bad_block {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    (p q : Seminorm ℂ (StrongDual ℂ G)) (hq : Continuous q)
    (hfail : ∀ r : Seminorm ℂ (StrongDual ℂ G), Continuous r → ¬ AbsSummingBound p r)
    (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) :
    ∃ (n : ℕ) (g : Fin n → StrongDual ℂ G), (∑ i, p (g i)) = L ∧
      ∀ x : G, (∀ f : StrongDual ℂ G, ‖f x‖ ≤ q f) → ∑ i, ‖g i x‖ ≤ δ := by
  let R : NNReal := ⟨L/δ,(div_pos hL hδ).le⟩
  have hbad := hfail (R • q) (hq.const_smul R)
  unfold AbsSummingBound at hbad
  push Not at hbad
  obtain ⟨n,f,c,hweak,hbig⟩ := hbad
  have hc : 0 ≤ c := by simpa using hweak 0 (fun y => by simpa only [zero_apply,norm_zero] using apply_nonneg (R • q) y)
  let u := ∑ i, p (f i)
  have hu : 0 < u := hc.trans_lt hbig
  let scale : ℂ := (L/u : ℝ)
  have hscale : ‖scale‖ = L/u := by exact (Complex.norm_real _).trans (Real.norm_of_nonneg (div_pos hL hu).le)
  refine ⟨n,fun i => scale • f i,?_,?_⟩
  · simp_rw [map_smul_eq_mul,hscale,← Finset.mul_sum]
    exact div_mul_cancel₀ _ hu.ne'
  intro x hx
  let e : StrongDual ℂ (StrongDual ℂ G) :=
    ⟨{ toFun := fun f => f x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
      continuous_eval_const x⟩
  have hR : ‖((L/δ : ℝ) : ℂ)‖ = L/δ := (Complex.norm_real _).trans (Real.norm_of_nonneg (div_pos hL hδ).le)
  have hle (f : StrongDual ℂ G) : ‖(((L/δ : ℝ) : ℂ) • e) f‖ ≤ (R • q) f := by
    change ‖((L/δ : ℝ) : ℂ) • f x‖ ≤ (L/δ) * q f
    rw [norm_smul,hR]
    exact mul_le_mul_of_nonneg_left (hx f) (div_pos hL hδ).le
  have hw := hweak _ hle
  change ∑ i, ‖((L/δ : ℝ) : ℂ) • f i x‖ ≤ c at hw
  simp_rw [norm_smul,hR,← Finset.mul_sum] at hw
  change ∑ i, ‖scale • f i x‖ ≤ δ
  simp_rw [norm_smul,hscale,← Finset.mul_sum]
  rw [div_mul_eq_mul_div,div_le_iff₀ hu]
  rw [div_mul_eq_mul_div,div_le_iff₀ hδ] at hw
  exact hw.trans (by nlinarith [mul_le_mul_of_nonneg_right hbig.le hδ.le])

-- The (DF) axiom turns a family with locally uniform bounds on every bounded
-- set into one continuous ℓ¹-valued map.
private theorem df_lone_map {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ 𝓝 0 ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) → (⋂ n, U n) ∈ 𝓝 0)
    (k : ℕ → ℕ) (g : (n : ℕ) → Fin (k n) → StrongDual ℂ G)
    (hb : ∀ S : Set G, IsVonNBounded ℂ S → ∃ M : ℝ, ∀ x ∈ S, ∀ N : ℕ,
      ∑ n ∈ Finset.range N, ∑ i, ‖g n i x‖ ≤ M) :
    ∃ T : G →L[ℂ] lp (fun _ : (n : ℕ) × Fin (k n) => ℂ) 1,
      ∀ n i x, T x ⟨n,i⟩ = g n i x := by
  let I := (n : ℕ) × Fin (k n)
  let coord (i : I) := g i.1 i.2
  let partialS (N : ℕ) : Seminorm ℂ G :=
    ∑ n ∈ Finset.range N, ∑ i, (g n i).toLinearMap.toSeminorm
  have hpartial (N : ℕ) (x : G) : partialS N x = ∑ n ∈ Finset.range N, ∑ i, ‖g n i x‖ := by
    simp [partialS]
  have hcont (N : ℕ) : Continuous (partialS N) :=
    Seminorm.continuous_finsetSum fun n _ => Seminorm.continuous_finsetSum (fun i _ => (g n i).continuous.norm)
  have hrows (x : G) : Summable (fun n => ∑ i, ‖g n i x‖) := by
    obtain ⟨M,hM⟩ := hb {x} (isVonNBounded_singleton (𝕜 := ℂ) x)
    exact summable_of_sum_range_le (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (hM x rfl)
  have hs (x : G) : Summable (fun i : I => ‖coord i x‖) := by
    apply (summable_sigma_of_nonneg (fun i => norm_nonneg (coord i x))).2
    exact ⟨fun _ => (hasSum_fintype _).summable,by simpa [coord,tsum_fintype] using hrows x⟩
  let t : G →ₗ[ℂ] lp (fun _ : I => ℂ) 1 :=
    { toFun := fun x => ⟨fun i => coord i x,memℓp_gen (by simpa using hs x)⟩
      map_add' := fun x y => by ext i; exact map_add (coord i) x y
      map_smul' := fun a x => by ext i; exact map_smul (coord i) a x }
  let p := (normSeminorm ℂ _).comp t
  let U (N : ℕ) := (partialS N).closedBall 0 1
  have hball : (⋂ n, U n) ⊆ p.closedBall 0 1 := by
    intro x hx
    rw [Seminorm.mem_closedBall_zero]
    have h1 : (∑' i : I, ‖coord i x‖) = ‖t x‖ := by
      simpa [t] using (lp.hasSum_norm (p := 1) (by norm_num) (t x)).tsum_eq
    change ‖t x‖ ≤ 1
    rw [← h1,(hs x).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
    simp only [tsum_fintype]
    exact (hrows x).tsum_le_of_sum_range_le fun n => (hpartial n x) ▸ ((partialS n).mem_closedBall_zero.mp (mem_iInter.mp hx n))
  have hU (n : ℕ) : U n ∈ 𝓝 0 ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n) := by
    refine ⟨?_,?_,(partialS n).balanced_closedBall_zero 1,(partialS n).convex_closedBall 0 1⟩
    · exact mem_of_superset ((Seminorm.continuous_iff one_pos).mp (hcont n)) ((partialS n).ball_subset_closedBall _ _)
    · rw [show U n = {x | partialS n x ≤ 1} from (partialS n).closedBall_zero_eq]
      exact isClosed_le (hcont n) continuous_const
  have habs (S : Set G) (hS : IsVonNBounded ℂ S) : Absorbs ℂ (⋂ n, U n) S := by
    obtain ⟨M,hM⟩ := hb S hS
    refine Absorbs.of_norm ⟨max M 1,fun c hc x hx => ?_⟩
    have hpos : 0 < ‖c‖ := zero_lt_one.trans_le ((le_max_right M 1).trans hc)
    apply (mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp hpos) _ _).2
    apply mem_iInter.mpr
    intro n
    rw [show U n = (partialS n).closedBall 0 1 from rfl,Seminorm.mem_closedBall_zero,map_smul_eq_mul,norm_inv,inv_mul_le_iff₀ hpos, mul_one]
    exact (hpartial n x).trans_le ((hM x hx n).trans ((le_max_left _ _).trans hc))
  have hp : Continuous p := Seminorm.continuous' (mem_of_superset (hDF U hU habs) hball)
  have ht : Continuous t := by
    apply continuous_of_continuousAt_zero t
    change Tendsto t (𝓝 0) (𝓝 (t 0))
    rw [map_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    change Tendsto (fun x => p x) (𝓝 0) (𝓝 0)
    exact hp.tendsto' 0 0 (map_zero p)
  exact ⟨⟨t,ht⟩,fun _ _ _ => rfl⟩

private theorem df_dual_abs_summing {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, IsVonNBounded ℂ (B n)) ∧ ∀ S : Set G, IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ 𝓝 0 ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) → (⋂ n, U n) ∈ 𝓝 0)
    (p : Seminorm ℂ (StrongDual ℂ G)) (hp : Continuous p) :
    ∃ q : Seminorm ℂ (StrongDual ℂ G), Continuous q ∧ AbsSummingBound p q := by
  classical
  obtain ⟨ι,_,P,hP⟩ := hN.1.1
  let := hP.topologicalAddGroup
  let := hP.continuousSMul
  let := hP.toPolynormableSpace
  obtain ⟨B,hBb,hcov⟩ := hB
  choose q hq hqB using (fun n => strongDual_seminorm_of_bounded G hN.1 (B n) (hBb n))
  let Q (n : ℕ) := (Finset.range (n+1)).sup q
  have hQ (n : ℕ) : Continuous (Q n) := Seminorm.continuous_finsetSup (fun i _ => hq i)
  by_contra hn
  have hfail (r : Seminorm ℂ (StrongDual ℂ G)) (hr : Continuous r) : ¬ AbsSummingBound p r :=
    fun h => hn ⟨r,hr,h⟩
  let δ (n : ℕ) := (1/2 : ℝ)^n
  choose k g hlarge hsmall using fun n => bad_block p (Q n) (hQ n) hfail (n+1) (δ n)
    (by positivity) (by dsimp [δ]; positivity)
  have hgeo : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let row (n : ℕ) (x : G) := ∑ i, ‖g n i x‖
  have hr0 (n : ℕ) (x : G) : 0 ≤ row n x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hunif (S : Set G) (hS : IsVonNBounded ℂ S) : ∃ M : ℝ, ∀ x ∈ S, ∀ N : ℕ,
      ∑ n ∈ Finset.range N, row n x ≤ M := by
    obtain ⟨m,hm⟩ := hcov S hS
    let head : Seminorm ℂ G := ∑ n ∈ Finset.range m, ∑ i, (g n i).toLinearMap.toSeminorm
    have hhead (x : G) : head x = ∑ n ∈ Finset.range m, row n x := by simp [head,row]
    have hhc : Continuous head := Seminorm.continuous_finsetSum fun n _ =>
      Seminorm.continuous_finsetSum fun i _ => (g n i).continuous.norm
    obtain ⟨M,_,hMS⟩ :=
      ((PolynormableSpace.withSeminorms ℂ G).isVonNBounded_iff_seminorm_bounded.mp hS) ⟨head,hhc⟩
    refine ⟨M + ∑' n, δ n,fun x hx N => ?_⟩
    have htail (i : ℕ) : row (m+i) x ≤ δ i := by
      apply (hsmall (m+i) x (fun f => (hqB m f x (hm hx)).trans ?_)).trans
      · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left i m)
      · exact (Finset.le_sup (f := q) (Finset.mem_range.mpr (by omega : m < m+i+1))) f
    calc
      _ ≤ ∑ n ∈ Finset.range (m+N), row n x := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_add_left N m)) (fun n _ _ => hr0 n x)
      _ = _ := Finset.sum_range_add _ _ _
      _ ≤ M + ∑' n, δ n := add_le_add ((hhead x).symm.trans_le (hMS x hx).le)
        ((Finset.sum_le_sum fun i _ => htail i).trans (hgeo.sum_le_tsum _ (fun i _ => by dsimp [δ]; positivity)))
  obtain ⟨T,hT⟩ := df_lone_map hDF k g hunif
  let I := (n : ℕ) × Fin (k n)
  have heq (i : I) : (lp.evalCLM ℂ (fun _ : I => ℂ) 1 i).comp T = g i.1 i.2 := by
    ext x
    exact hT _ _ _
  have hs : Summable (fun i : I => p (g i.1 i.2)) :=
    (coordinates_abs_summable hN T p hp).congr (fun i => congrArg p (heq i))
  have hb := ((summable_sigma_of_nonneg (fun i : I => apply_nonneg p (g i.1 i.2))).mp hs).2
  simp only [tsum_fintype] at hb
  simp_rw [hlarge] at hb
  obtain ⟨n,hn⟩ := exists_nat_gt (∑' n : ℕ, ((n : ℝ)+1))
  have h := hb.le_tsum n (fun _ _ => by positivity)
  linarith

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (_hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G)) :
    IsNuclear (StrongDual ℂ G) := by
  have hF := strongDual_isHLCS G hN.1
  apply nuclear_of_quasinuclear_domination _ hF
  exact quasinuclear_domination_of_abs_summing _ hF (df_dual_abs_summing hN hB hDF)
