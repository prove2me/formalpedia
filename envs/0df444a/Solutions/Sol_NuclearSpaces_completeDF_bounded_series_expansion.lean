-- Prove2me | solution 1 for NuclearSpaces.completeDF_bounded_series_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:20:33.093763+00:00
-- url     : https://prove2.me/submissions/99586601-e653-40ce-a920-94f6563b0692

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_banach_map_representation
import Theorems.Thm_MasulloGRH_strongDual_seminorm_of_bounded
import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
import Theorems.Thm_MasulloGRH_strongDual_isHLCS
import Theorems.Thm_MasulloGRH_quasiCompleteNuclear_strongBidual_bounded_repr
import Theorems.Thm_MasulloGRH_quasinuclear_domination_of_abs_summing

set_option autoImplicit false

open MasulloGRH Set Filter Topology Bornology
open scoped Pointwise

private theorem lp_one_norm {ι : Type*} (v : lp (fun _ : ι => ℂ) 1) :
    ‖v‖ = ∑' i, ‖v i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by simp) v

private theorem lp_one_summable {ι : Type*} (v : lp (fun _ : ι => ℂ) 1) :
    Summable (fun i => ‖v i‖) := by
  simpa using (memℓp_gen_iff (p := 1) (by simp)).1 v.property

private theorem nuclearDF_summable_majorant {G I : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hN : IsNuclear G)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧
        Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (T : ℕ → Finset I) (hT : ∀ s : Finset I, ∃ n, s ⊆ T n)
    (f : I → StrongDual ℂ G)
    (hweak : ∀ S : Set G, IsVonNBounded ℂ S → ∃ C : ℝ,
      ∀ x ∈ S, ∀ s : Finset I, ∑ i ∈ s, ‖f i x‖ ≤ C)
    (B : Set G) (hB : IsVonNBounded ℂ B) :
    ∃ b : I → ℝ, (∀ i, 0 ≤ b i) ∧ Summable b ∧ ∀ i x, x ∈ B → ‖f i x‖ ≤ b i := by
  classical
  obtain ⟨_, _, P, hP⟩ := hN.1.1
  let : IsTopologicalAddGroup G := hP.topologicalAddGroup
  let : ContinuousSMul ℂ G := hP.continuousSMul
  let : PolynormableSpace ℂ G := hP.toPolynormableSpace
  let : Module ℝ G := Module.restrictScalars ℝ ℂ G
  let : IsScalarTower ℝ ℂ G := IsScalarTower.restrictScalars ℝ ℂ G
  -- The countable intersection of finite-coordinate balls is a neighborhood by (DF).
  let Pfin (s : Finset I) : Seminorm ℂ G :=
    ∑ i ∈ s, (normSeminorm ℂ ℂ).comp (f i).toLinearMap
  have hPfin (s : Finset I) (x : G) : Pfin s x = ∑ i ∈ s, ‖f i x‖ := by
    simp [Pfin]
  have hcfin (s : Finset I) : Continuous (Pfin s) := by
    simp_rw [show (Pfin s : G → ℝ) = fun x => ∑ i ∈ s, ‖f i x‖ from funext (hPfin s)]
    exact continuous_finsetSum _ fun i _ => (f i).continuous.norm
  let U (n : ℕ) : Set G := (Pfin (T n)).closedBall 0 1
  have hU (n : ℕ) (x : G) : x ∈ U n ↔ Pfin (T n) x ≤ 1 := by
    change _ ∈ (Pfin (T n)).closedBall 0 1 ↔ _
    rw [Seminorm.closedBall_zero_eq]
    rfl
  have hnb (n : ℕ) : U n ∈ 𝓝 (0 : G) := by
    apply Filter.mem_of_superset
      (IsOpen.mem_nhds (isOpen_lt (hcfin (T n)) continuous_const) (by simp : Pfin (T n) 0 < 1))
    exact fun x hx => (hU n x).2 (le_of_lt hx)
  have hclosed (n : ℕ) : IsClosed (U n) := by
    change IsClosed ((Pfin (T n)).closedBall 0 1)
    rw [Seminorm.closedBall_zero_eq]
    exact isClosed_le (hcfin (T n)) continuous_const
  have hbor (S : Set G) (hS : IsVonNBounded ℂ S) : Absorbs ℂ (⋂ n, U n) S := by
    obtain ⟨C, hC⟩ := hweak S hS
    refine Absorbs.of_norm ⟨max 1 C, fun a ha x hx => ?_⟩
    have hapos : 0 < ‖a‖ := zero_lt_one.trans_le ((le_max_left 1 C).trans ha)
    have hane : a ≠ 0 := norm_pos_iff.1 hapos
    refine ⟨a⁻¹ • x, mem_iInter.2 fun n => (hU n _).2 ?_, by simp [smul_inv_smul₀ hane]⟩
    rw [map_smul_eq_mul, norm_inv, inv_mul_le_iff₀ hapos, mul_one, hPfin]
    exact (hC x hx (T n)).trans ((le_max_right 1 C).trans ha)
  have hV := hDF U (fun n => ⟨hnb n, hclosed n, (Pfin (T n)).balanced_closedBall_zero 1,
    (Pfin (T n)).convex_closedBall 0 1⟩) hbor
  have hfmem (x : G) : Memℓp (fun i => f i x) 1 := by
    obtain ⟨C, hC⟩ := hweak {x} (isVonNBounded_singleton x)
    apply (memℓp_gen_iff'' (p := 1) (by simp)).2
    exact ⟨max 0 C, le_max_left _ _, fun s => by simpa using (hC x rfl s).trans (le_max_right 0 C)⟩
  let L : G →ₗ[ℂ] lp (fun _ : I => ℂ) 1 :=
    { toFun := fun x => ⟨fun i => f i x, hfmem x⟩
      map_add' := fun x y => by ext i; exact map_add (f i) x y
      map_smul' := fun a x => by ext i; exact map_smul (f i) a x }
  have hL (x : G) (hx : x ∈ ⋂ n, U n) : ‖L x‖ ≤ 1 := by
    rw [lp_one_norm]
    apply (lp_one_summable (L x)).tsum_le_of_sum_le
    intro s
    obtain ⟨n, hn⟩ := hT s
    refine (Finset.sum_le_sum_of_subset_of_nonneg hn (fun _ _ _ => norm_nonneg _)).trans ?_
    change ∑ i ∈ T n, ‖f i x‖ ≤ 1
    rw [← hPfin]
    exact (hU n x).1 (mem_iInter.1 hx n)
  have hLc : Continuous L := by
    apply continuous_of_continuousAt_zero L
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hzero : Tendsto (fun x : G => ((↑(2 / ε) : ℂ) • x)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun x : G => ((↑(2 / ε) : ℂ) • x)) :=
        continuous_const.smul continuous_id
      simpa only [smul_zero] using hc.tendsto 0
    filter_upwards [hzero.eventually_mem hV] with x hx
    have hb := hL _ hx
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hb
    rw [map_zero, dist_zero_right]
    have heq : (2 / ε) * (ε / 2) = 1 := by field_simp
    exact (le_of_mul_le_mul_left (hb.trans_eq heq.symm) (by positivity : 0 < 2/ε)).trans_lt
      (half_lt_self hε)
  let u : G →L[ℂ] lp (fun _ : I => ℂ) 1 := ⟨L, hLc⟩
  obtain ⟨p, φ, v, c, hp, hφ, hv, hc, hrep⟩ := nuclear_banach_map_representation G _ hN u
  obtain ⟨M, hM, hpB⟩ :=
    (PolynormableSpace.withSeminorms ℂ G).isVonNBounded_iff_seminorm_bounded.1 hB ⟨p, hp⟩
  let a (n : ℕ) := ‖c n‖ * M
  have ha : Summable a := hc.mul_right M
  have hano (n : ℕ) : 0 ≤ a n := mul_nonneg (norm_nonneg _) hM.le
  let A (i : I) (n : ℕ) := a n * ‖v n i‖
  have hAno (i : I) (n : ℕ) : 0 ≤ A i n := mul_nonneg (hano n) (norm_nonneg _)
  have hAs (i : I) : Summable (A i) := ha.of_nonneg_of_le (hAno i) fun n =>
    mul_le_of_le_one_right (hano n) ((lp.norm_apply_le_norm one_ne_zero (v n) i).trans (hv n))
  let b (i : I) := ∑' n, A i n
  have hbpos (i : I) : 0 ≤ b i := tsum_nonneg (hAno i)
  have hbs : Summable b := by
    apply summable_of_sum_le hbpos (c := ∑' n, a n)
    intro s
    change ∑ i ∈ s, ∑' n, A i n ≤ _
    rw [← Summable.tsum_finsetSum (fun i _ => hAs i)]
    apply Summable.tsum_mono (summable_sum fun i _ => hAs i) ha
    intro n
    change ∑ i ∈ s, a n * ‖v n i‖ ≤ a n
    rw [← Finset.mul_sum]
    apply mul_le_of_le_one_right (hano n)
    exact ((lp_one_summable (v n)).sum_le_tsum s (fun i _ => norm_nonneg _)).trans
      ((lp_one_norm (v n)).ge.trans (hv n))
  refine ⟨b, hbpos, hbs, fun i x hx => ?_⟩
  let read : lp (fun _ : I => ℂ) 1 →L[ℂ] ℂ := lp.evalCLM ℂ _ 1 i
  have hcoord : HasSum (fun n => (c n * φ n x) * v n i) (f i x) :=
    read.hasSum (hrep x)
  have hterm (n : ℕ) : ‖(c n * φ n x) * v n i‖ ≤ A i n := by
    simp only [norm_mul, A, a]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left ((hφ n x).trans (hpB x hx).le) (norm_nonneg _)
  have hsumm := (hAs i).of_nonneg_of_le (fun n => norm_nonneg _) hterm
  rw [← hcoord.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_mono (hAs i) hterm)

private theorem strong_dual_abs_summing {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hN : IsNuclear G)
    (B : ℕ → Set G) (hB : ∀ n, IsVonNBounded ℂ (B n))
    (hcover : ∀ S : Set G, IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧
        Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G)) :
    ∀ p : Seminorm ℂ (StrongDual ℂ G), Continuous p →
      ∃ q : Seminorm ℂ (StrongDual ℂ G), Continuous q ∧
        ∀ (n : ℕ) (x : Fin n → StrongDual ℂ G) (c : ℝ),
          (∀ f : StrongDual ℂ (StrongDual ℂ G), (∀ y, ‖f y‖ ≤ q y) →
            (∑ i, ‖f (x i)‖) ≤ c) → (∑ i, p (x i)) ≤ c := by
  classical
  obtain ⟨_, _, PG, hPG⟩ := hN.1.1
  let : ContinuousSMul ℂ G := hPG.continuousSMul
  let F := StrongDual ℂ G
  let ev (x : G) : StrongDual ℂ F :=
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_eval_const x }
  choose P hP hdom using (fun n => strongDual_seminorm_of_bounded G hN.1 (B n) (hB n))
  let Q (n : ℕ) : Seminorm ℂ F := (Finset.range (n + 1)).sup P
  have hQ (n : ℕ) : Continuous (Q n) := Seminorm.continuous_finsetSup fun i _ => hP i
  have hP_Q {n m : ℕ} (hm : m ≤ n) (f : F) : P m f ≤ Q n f :=
    (Finset.le_sup (f := P) (Finset.mem_range.2 (Nat.lt_succ_of_le hm))) f
  let a (n : ℕ) : ℝ := 2 ^ n
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let q (n : ℕ) : Seminorm ℂ F :=
    (Q n).comp ((↑(a n) : ℂ) • (LinearMap.id : F →ₗ[ℂ] F))
  have hq (n : ℕ) (f : F) : q n f = a n * Q n f := by
    change Q n ((↑(a n) : ℂ) • f) = _
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (ha n).le]
  have hcq (n : ℕ) : Continuous (q n) := by
    have hc : Continuous (fun x : F => a n * Q n x) := continuous_const.mul (hQ n)
    exact hc.congr (fun x => (hq n x).symm)
  intro p hp
  by_contra! hbad
  have hcounter (n : ℕ) :
      ∃ (k : ℕ) (x : Fin k → F) (c : ℝ),
        (∀ f : StrongDual ℂ F, (∀ y, ‖f y‖ ≤ q n y) → (∑ i, ‖f (x i)‖) ≤ c) ∧
        c < ∑ i, p (x i) := hbad (q n) (hcq n)
  choose k x c hweak hlarge using hcounter
  let z (n : ℕ) : ℝ := ∑ i, p (x n i)
  have hc (n : ℕ) : 0 ≤ c n := by
    simpa using hweak n 0 (fun y => by simp)
  have hz (n : ℕ) : 0 < z n := (hc n).trans_lt (hlarge n)
  let y (n : ℕ) (i : Fin (k n)) : F := (↑(z n)⁻¹ : ℂ) • x n i
  have hmass (n : ℕ) : (∑ i, p (y n i)) = 1 := by
    simp only [y, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (hz n).le)]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (hz n).ne'
  have htail (n m : ℕ) (hm : m ≤ n) (w : G) (hw : w ∈ B m) :
      (∑ i, ‖y n i w‖) ≤ (a n)⁻¹ := by
    have hbound : ∀ f : F, ‖((↑(a n) : ℂ) • ev w) f‖ ≤ q n f := by
      intro f
      rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (ha n).le, hq]
      change a n * ‖f w‖ ≤ a n * Q n f
      exact mul_le_mul_of_nonneg_left ((hdom m f w hw).trans (hP_Q hm f)) (ha n).le
    have ht := hweak n ((↑(a n) : ℂ) • ev w) hbound
    simp only [smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (ha n).le,
      show ∀ f : F, ev w f = f w from fun _ => rfl, ← Finset.mul_sum] at ht
    simp only [y, smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (hz n).le), ← Finset.mul_sum]
    rw [inv_mul_le_iff₀ (hz n), mul_comm, le_inv_mul_iff₀ (ha n)]
    calc
      a n * (∑ i, ‖x n i w‖) ≤ c n := ht
      _ ≤ z n := (hlarge n).le
  let I := Σ n, Fin (k n)
  let T (n : ℕ) : Finset I := (Finset.range n).sigma (fun _ => Finset.univ)
  have hT (s : Finset I) : ∃ n, s ⊆ T n := by
    refine ⟨s.sup Sigma.fst + 1, fun i hi => ?_⟩
    exact Finset.mem_sigma.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hi)),
      Finset.mem_univ _⟩
  let f (i : I) : F := y i.1 i.2
  have hG : Summable (fun n => (a n)⁻¹) := by
    have h := summable_geometric_of_norm_lt_one (x := (2 : ℝ)⁻¹) (by norm_num)
    simpa only [a, inv_pow] using h
  have hbounded (S : Set G) (hS : IsVonNBounded ℂ S) :
      ∃ C : ℝ, ∀ w ∈ S, ∀ s : Finset I, ∑ i ∈ s, ‖f i w‖ ≤ C := by
    obtain ⟨m, hm⟩ := hcover S hS
    let D (n : ℕ) : ℝ := if n < m then ∑ i, P m (y n i) else 0
    have hD (n : ℕ) : 0 ≤ D n := by
      dsimp [D]
      split
      · exact Finset.sum_nonneg fun i _ => apply_nonneg (P m) (y n i)
      · exact le_rfl
    have hsD : Summable D :=
      summable_of_ne_finset_zero (s := Finset.range m) fun n hn =>
        if_neg (fun h => hn (Finset.mem_range.2 h))
    let M (n : ℕ) := (a n)⁻¹ + D n
    have hM : Summable M := hG.add hsD
    have hMpos (n : ℕ) : 0 ≤ M n := add_nonneg (inv_nonneg.mpr (ha n).le) (hD n)
    refine ⟨∑' n, M n, fun w hw s => ?_⟩
    obtain ⟨N, hN'⟩ := hT s
    refine (Finset.sum_le_sum_of_subset_of_nonneg hN' (fun _ _ _ => norm_nonneg _)).trans ?_
    dsimp only [T]
    rw [Finset.sum_sigma]
    refine (Finset.sum_le_sum fun n _ => ?_).trans (hM.sum_le_tsum _ (fun n _ => hMpos n))
    change (∑ i : Fin (k n), ‖y n i w‖) ≤ M n
    by_cases h : n < m
    · refine (Finset.sum_le_sum fun i _ => hdom m _ _ (hm hw)).trans ?_
      exact le_add_of_nonneg_left (inv_nonneg.mpr (ha n).le) |>.trans_eq (by simp [M, D, h])
    · exact (htail n m (le_of_not_gt h) w (hm hw)).trans (le_add_of_nonneg_right (hD n))
  obtain ⟨S, C, hS, hC, hpolar⟩ := strongDual_seminorm_le_polar G hN.1 p hp
  obtain ⟨b, hb, hbs, hfb⟩ := nuclearDF_summable_majorant hN hDF T hT f hbounded S hS
  have hbound (i : I) : p (f i) ≤ C * b i := hpolar (f i) (b i) (hb i) (hfb i)
  obtain ⟨N, hN'⟩ := exists_nat_gt (∑' i, C * b i)
  have hsum : (∑ i ∈ T N, p (f i)) = N := by
    dsimp only [T]
    rw [Finset.sum_sigma]
    change (∑ n ∈ Finset.range N, ∑ i : Fin (k n), p (y n i)) = _
    simp [hmass]
  have hfinal := (Finset.sum_le_sum (s := T N) fun i _ => hbound i).trans
    ((hbs.mul_left C).sum_le_tsum (T N) fun i _ => mul_nonneg hC (hb i))
  exact (not_lt_of_ge (hsum ▸ hfinal)) hN'

private theorem complete_of_filters {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] (hC : IsCompleteTVS E) : CompleteSpace E := by
  constructor
  intro f hf
  obtain ⟨hbot, hdiff⟩ := (IsUniformAddGroup.cauchy_iff_tendsto f).1 hf
  refine hC.2 f ⟨hbot, fun U hU => ?_⟩
  obtain ⟨A, hA, B, hB, hsub⟩ := mem_prod_iff.1 (hdiff hU)
  exact ⟨A ∩ B, inter_mem hA hB, fun x hx y hy => hsub (show (x, y) ∈ A ×ˢ B from ⟨hx.1, hy.2⟩)⟩

private theorem bounded_sequence_extension {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hC : IsCompleteTVS E) (hE : IsLocallyConvexTopology E inferInstance) (y : ℕ → E)
    (hy : IsVonNBounded ℂ (range y)) :
    ∃ L : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] E,
      ∀ z : lp (fun _ : ℕ => ℂ) 1, HasSum (fun i => z i • y i) (L z) := by
  obtain ⟨_, _, P, hP⟩ := hE
  let : IsTopologicalAddGroup E := hP.topologicalAddGroup
  let : ContinuousSMul ℂ E := hP.continuousSMul
  let : T2Space E := hC.1
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := complete_of_filters hC
  choose M hM hyM using hP.isVonNBounded_iff_seminorm_bounded.1 hy
  have hbound (z : lp (fun _ : ℕ => ℂ) 1) (k : _) (s : Finset ℕ) :
      P k (∑ i ∈ s, z i • y i) ≤ M k * ∑ i ∈ s, ‖z i‖ := by
    rw [Finset.mul_sum]
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine (map_add_le_add (P k) _ _).trans (add_le_add ?_ ih)
      rw [map_smul_eq_mul, mul_comm (M k)]
      exact mul_le_mul_of_nonneg_left (hyM k _ (mem_range_self _)).le (norm_nonneg _)
  have hs (z : lp (fun _ : ℕ => ℂ) 1) : Summable (fun i => z i • y i) := by
    apply summable_iff_cauchySeq_finset.2
    apply cauchySeq_finset_iff_sum_vanishing.2
    intro W hW
    obtain ⟨⟨J, ε⟩, hε, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hW
    let C : ℝ := 1 + ∑ k ∈ J, M k
    have hC : 0 < C := by
      dsimp [C]
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun k _ => (hM k).le)
    have hMC (k : _) (hk : k ∈ J) : M k ≤ C :=
      (Finset.single_le_sum (fun j _ => (hM j).le) hk).trans (le_add_of_nonneg_left zero_le_one)
    obtain ⟨t, ht⟩ := summable_iff_vanishing_norm.1 (lp_one_summable z) (ε / C) (div_pos hε hC)
    refine ⟨t, fun s hs => hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    apply Seminorm.finset_sup_apply_lt hε
    intro k hk
    have hsmall : (∑ i ∈ s, ‖z i‖) < ε / C := by
      simpa only [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (z i))]
        using ht s hs
    refine (hbound z k s).trans_lt ?_
    calc
      M k * ∑ i ∈ s, ‖z i‖ ≤ C * ∑ i ∈ s, ‖z i‖ :=
        mul_le_mul_of_nonneg_right (hMC k hk) (Finset.sum_nonneg fun i _ => norm_nonneg _)
      _ < ε := by
        have heq : C * (ε / C) = ε := by field_simp
        exact (mul_lt_mul_of_pos_left hsmall hC).trans_eq heq
  let L : lp (fun _ : ℕ => ℂ) 1 →ₗ[ℂ] E :=
    { toFun := fun z => ∑' i, z i • y i
      map_add' := fun a b => by
        change (∑' i, (a i + b i) • y i) = _
        simp_rw [add_smul]
        exact (hs a).tsum_add (hs b)
      map_smul' := fun a z => by
        change (∑' i, (a * z i) • y i) = a • (∑' i, z i • y i)
        simp_rw [mul_smul]
        exact ((hs z).hasSum.const_smul a).tsum_eq }
  have hLp (k : _) (z : lp (fun _ : ℕ => ℂ) 1) : P k (L z) ≤ M k * ‖z‖ := by
    apply le_of_tendsto ((hP.continuous_seminorm k).continuousAt.tendsto.comp ((hs z).hasSum))
    refine Eventually.of_forall fun s => (hbound z k s).trans ?_
    rw [lp_one_norm]
    exact mul_le_mul_of_nonneg_left
      ((lp_one_summable z).sum_le_tsum s (fun i _ => norm_nonneg _)) (hM k).le
  have hLc : Continuous L := by
    apply hP.continuous_of_continuous_comp L
    intro k
    apply Seminorm.continuous' (r := 1)
    rw [Seminorm.closedBall_zero_eq]
    refine mem_of_superset (Metric.ball_mem_nhds (0 : lp (fun _ : ℕ => ℂ) 1)
      (show 0 < 1 / M k from one_div_pos.mpr (hM k))) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact (hLp k z).trans (by
      have h := (lt_div_iff₀ (hM k)).1 hz
      simpa only [mul_comm] using h.le)
  exact ⟨⟨L, hLc⟩, fun z => (hs z).hasSum⟩

private theorem rotate_to_norm (z : ℂ) :
    ∃ a : ℂ, ‖a‖ ≤ 1 ∧ (a * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℂ := (starRingEnd ℂ) z / (‖z‖ : ℂ)
  refine ⟨a, ?_, ?_⟩
  · change ‖(starRingEnd ℂ) z / (‖z‖ : ℂ)‖ ≤ 1
    rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne']
  · change (((starRingEnd ℂ) z / (‖z‖ : ℂ)) * z).re = ‖z‖
    have hc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_mul_eq_mul_div, RCLike.conj_mul]
    change (((‖z‖ : ℂ) ^ 2) / (‖z‖ : ℂ)).re = ‖z‖
    rw [sq, mul_div_cancel_right₀ _ hc]
    exact Complex.ofReal_re _


private theorem compact_l1_box (c : ℕ → ℝ) (hc : Summable c) :
    IsCompact {z : lp (fun _ : ℕ => ℂ) 1 | ∀ i, ‖z i‖ ≤ c i} := by
  classical
  let : ∀ i, CompactSpace {z : ℂ // ‖z‖ ≤ c i} := fun i => by
    have h : IsCompact {z : ℂ | ‖z‖ ≤ c i} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ℂ) (c i)
    exact isCompact_iff_compactSpace.1 h
  let a : (∀ j, {z : ℂ // ‖z‖ ≤ c j}) → lp (fun _ : ℕ => ℂ) 1 := fun z => ⟨fun n => (z n).1, by
    apply (memℓp_gen_iff (p := 1) (by simp)).2
    simpa using hc.of_nonneg_of_le (fun i => norm_nonneg (z i).1) (fun i => (z i).2)⟩
  have hsum : ∀ z : (∀ j, {z : ℂ // ‖z‖ ≤ c j}), HasSum (fun i => lp.single 1 i (z i).1) (a z) :=
    fun z => lp.hasSum_single (p := 1) (by simp) (a z)
  have hcont : Continuous a := by
    have h : Continuous (fun z : (∀ j, {z : ℂ // ‖z‖ ≤ c j}) => ∑' i, lp.single 1 i (z i).1) := by
      have hco (i : ℕ) : Continuous (fun z : (∀ j, {z : ℂ // ‖z‖ ≤ c j}) => (z i).1) :=
        continuous_subtype_val.comp (continuous_apply i)
      exact continuous_tsum (fun i =>
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 i).continuous.comp (hco i)) hc
        (fun i z => by
          rw [lp.norm_single zero_lt_one]
          exact (z i).2)
    exact h.congr (fun z => (hsum z).tsum_eq)
  have heq : range a = {z | ∀ i, ‖z i‖ ≤ c i} := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact fun i => (q i).2
    · intro hz
      let q : (∀ j, {z : ℂ // ‖z‖ ≤ c j}) := fun i => ⟨z i, hz i⟩
      exact ⟨q, lp.ext rfl⟩
  rw [← heq, ← image_univ]
  exact isCompact_univ.image hcont

private theorem expansion_of_domination {G : Type*} [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (y : ℕ → G) (hy : IsVonNBounded ℂ (range y))
    (c : ℕ → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc : Summable c) (x : G)
    (hdom : ∀ f : StrongDual ℂ G, ‖f x‖ ≤ ∑' i, c i * ‖f (y i)‖) :
    ∃ a : ℕ → ℂ, (∀ i, ‖a i‖ ≤ c i) ∧ HasSum (fun i => a i • y i) x := by
  classical
  obtain ⟨L, hL⟩ := bounded_sequence_extension hC hN.1.1 y hy
  obtain ⟨_, _, P, hP⟩ := hN.1.1
  let : T2Space G := hC.1
  let : IsTopologicalAddGroup G := hP.topologicalAddGroup
  let : ContinuousSMul ℂ G := hP.continuousSMul
  let : LocallyConvexSpace ℝ G := hP.toLocallyConvexSpace
  let A : Set (lp (fun _ : ℕ => ℂ) 1) := {a | ∀ i, ‖a i‖ ≤ c i}
  have hAconv : Convex ℝ A := by
    intro a ha b hb u v hu hv huv i
    change ‖u • a i + v • b i‖ ≤ c i
    calc
      ‖u • a i + v • b i‖ ≤ ‖u • a i‖ + ‖v • b i‖ := norm_add_le _ _
      _ ≤ u * c i + v * c i := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hu, Real.norm_of_nonneg hv]
        exact add_le_add (mul_le_mul_of_nonneg_left (ha i) hu) (mul_le_mul_of_nonneg_left (hb i) hv)
      _ = c i := by rw [← add_mul, huv, one_mul]
  have hDconv : Convex ℝ (L '' A) := hAconv.linear_image (L.toLinearMap.restrictScalars ℝ)
  have hDclosed : IsClosed (L '' A) := ((compact_l1_box c hc).image L.continuous).isClosed
  suffices hxD : x ∈ L '' A by
    obtain ⟨a, ha, rfl⟩ := hxD
    exact ⟨a, ha, hL a⟩
  by_contra hxD
  obtain ⟨f, r, hsep, hlt⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hDconv hDclosed hxD
  choose u hu huf using (fun i => rotate_to_norm (f (y i)))
  let a (i : ℕ) : ℂ := (c i : ℂ) * u i
  have ha (i : ℕ) : ‖a i‖ ≤ c i := by
    change ‖(c i : ℂ) * u i‖ ≤ c i
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 i)]
    exact mul_le_of_le_one_right (hc0 i) (hu i)
  let z : lp (fun _ : ℕ => ℂ) 1 := ⟨a, by
    apply (memℓp_gen_iff (p := 1) (by simp)).2
    simpa using hc.of_nonneg_of_le (fun i => norm_nonneg (a i)) ha⟩
  have hsum : HasSum (fun i => c i * ‖f (y i)‖) (f (L z)).re := by
    have h := Complex.reCLM.hasSum (f.hasSum (hL z))
    have hfun : (fun i : ℕ => Complex.reCLM (f (z i • y i))) =
        fun i => c i * ‖f (y i)‖ := by
      funext i
      change (f (a i • y i)).re = _
      rw [map_smul, smul_eq_mul]
      change (((c i : ℂ) * u i) * f (y i)).re = _
      rw [mul_assoc, Complex.re_ofReal_mul, huf i]
    rw [hfun] at h
    simpa only [Complex.reCLM_apply] using h
  have hn : r < ∑' i, c i * ‖f (y i)‖ :=
    (hlt.trans_le (RCLike.re_le_norm (f x))).trans_le (hdom f)
  rw [hsum.tsum_eq] at hn
  exact hn.not_gt (hsep (L z) (mem_image_of_mem L (show z ∈ A from ha)))

theorem solution
    (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hB : ∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n)
    (hDF : ∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      ∀ x ∈ B, ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ c n) ∧
        HasSum (fun n => a n • y n) x := by
  classical
  obtain ⟨T, hTb, hfund⟩ := hB
  let hF := strongDual_isHLCS G hN.1
  have hAS := strong_dual_abs_summing hN T hTb hfund hDF
  obtain ⟨p, hp, hpB⟩ := strongDual_seminorm_of_bounded G hN.1 B hBb
  obtain ⟨q, Φ, c, hq, hc0, hc, hΦ, hdom⟩ :=
    quasinuclear_domination_of_abs_summing (StrongDual ℂ G) hF hAS p hp
  have hquasi : IsQuasiComplete G := ⟨hC.1, fun f hf _ => hC.2 f hf⟩
  obtain ⟨D, hD, hrepr⟩ := quasiCompleteNuclear_strongBidual_bounded_repr G hquasi hN q hq
  choose y hy hyf using (fun n => hrepr (Φ n) (hΦ n))
  have hby : IsVonNBounded ℂ (range y) := hD.subset (range_subset_iff.2 hy)
  refine ⟨y, c, hby, hc0, hc, fun x hx => ?_⟩
  apply expansion_of_domination hC hN y hby c hc0 hc
  intro f
  exact (hpB f x hx).trans (by simpa only [hyf] using hdom f)
