-- Prove2me | solution 1 for LesHouchesWidth.jacobianEntry_eq_sum_over_paths_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T13:51:41.808704+00:00
-- url     : https://prove2.me/submissions/659746ed-0cf2-43b3-b21f-e28a2251b866

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

set_option autoImplicit false

namespace LesHouchesWidth
namespace PV5d

abbrev PP (n : ℕ → ℕ) (k : ℕ) : Type := (ℓ : Fin (k + 1)) → Fin (n ℓ.val)

noncomputable def chain {n : ℕ → ℕ} (T : (ℓ : ℕ) → Fin (n (ℓ + 1)) → Fin (n ℓ) → ℝ) :
    (k : ℕ) → Fin (n k) → Fin (n 0) → ℝ
  | 0 => fun i p => if i = p then 1 else 0
  | k + 1 => fun i p => ∑ j, T k i j * chain T k j p

noncomputable def pathProd {n : ℕ → ℕ} (T : (ℓ : ℕ) → Fin (n (ℓ + 1)) → Fin (n ℓ) → ℝ)
    (k : ℕ) (γ : PP n k) : ℝ :=
  ∏ ℓ : Fin k, T ℓ.val (γ ℓ.succ) (γ ℓ.castSucc)

theorem snoc_zero' {n : ℕ → ℕ} {k : ℕ} (f : PP n k) (a : Fin (n (k + 1))) :
    (Fin.snoc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) f a 0 : Fin (n 0)) = f 0 :=
  Fin.snoc_castSucc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) (p := f) (x := a) (i := 0)

theorem snoc_succ_castSucc {n : ℕ → ℕ} {k : ℕ} (f : PP n k) (a : Fin (n (k + 1)))
    (ℓ : Fin k) :
    (Fin.snoc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) f a ℓ.castSucc.succ :
      Fin (n (ℓ.val + 1))) = f ℓ.succ :=
  Fin.snoc_castSucc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) (p := f) (x := a) (i := ℓ.succ)

theorem snoc_castSucc_castSucc {n : ℕ → ℕ} {k : ℕ} (f : PP n k) (a : Fin (n (k + 1)))
    (ℓ : Fin (k + 1)) :
    (Fin.snoc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) f a ℓ.castSucc :
      Fin (n ℓ.val)) = f ℓ :=
  Fin.snoc_castSucc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) (p := f) (x := a) (i := ℓ)

theorem snoc_last' {n : ℕ → ℕ} {k : ℕ} (f : PP n k) (a : Fin (n (k + 1))) :
    (Fin.snoc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) f a (Fin.last (k + 1)) :
      Fin (n (k + 1))) = a :=
  Fin.snoc_last (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) (p := f) (x := a)

theorem pathProd_snoc {n : ℕ → ℕ} (T : (ℓ : ℕ) → Fin (n (ℓ + 1)) → Fin (n ℓ) → ℝ)
    (k : ℕ) (f : PP n k) (a : Fin (n (k + 1))) :
    pathProd T (k + 1) (Fin.snoc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) f a) =
      pathProd T k f * T k a (f (Fin.last k)) := by
  unfold pathProd
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have h1 := snoc_succ_castSucc f a ℓ
    have h2 := snoc_castSucc_castSucc f a ℓ.castSucc
    simp only [Fin.val_castSucc] at h1 h2 ⊢
    rw [h1, h2]
  · have h1 := snoc_last' f a
    have h2 := snoc_castSucc_castSucc f a (Fin.last k)
    simp only [Fin.succ_last, Fin.val_last] at h1 h2 ⊢
    rw [h1, h2]

open Classical in
theorem chain_eq_sum {n : ℕ → ℕ} (T : (ℓ : ℕ) → Fin (n (ℓ + 1)) → Fin (n ℓ) → ℝ) (k : ℕ)
    (i : Fin (n k)) (p : Fin (n 0)) :
    chain T k i p = ∑ γ : PP n k,
      if (γ 0).val = p.val ∧ (γ (Fin.last k)).val = i.val then pathProd T k γ else 0 := by
  induction k with
  | zero =>
    rw [← (Equiv.piUnique (fun ℓ : Fin 1 => Fin (n ℓ.val))).symm.sum_comp]
    have h0 : ∀ j : Fin (n 0),
        (((Equiv.piUnique (fun ℓ : Fin 1 => Fin (n ℓ.val))).symm j) 0).val = j.val :=
      fun j => rfl
    have h1 : ∀ j : Fin (n 0),
        (((Equiv.piUnique (fun ℓ : Fin 1 => Fin (n ℓ.val))).symm j) (Fin.last 0)).val = j.val :=
      fun j => rfl
    have hp : ∀ j : Fin (n 0), pathProd T 0 ((Equiv.piUnique (fun ℓ : Fin 1 => Fin (n ℓ.val))).symm j) = 1 :=
      fun j => by simp [pathProd]
    simp only [h0, h1, hp, Fin.val_inj]
    refine Eq.trans ?_ (Fintype.sum_eq_single p (fun b hb => by simp [hb])).symm
    simp [chain, eq_comm]
  | succ k ih =>
    rw [← (Fin.snocEquiv (fun ℓ : Fin (k + 2) => Fin (n ℓ.val))).sum_comp,
      Fintype.sum_prod_type]
    have key : ∀ (a : Fin (n (k + 1))) (f : PP n k),
        (if (((Fin.snocEquiv (fun ℓ : Fin (k + 2) => Fin (n ℓ.val))) (a, f)) 0).val = p.val ∧
            (((Fin.snocEquiv (fun ℓ : Fin (k + 2) => Fin (n ℓ.val))) (a, f))
              (Fin.last (k + 1))).val = i.val
          then pathProd T (k + 1) ((Fin.snocEquiv (fun ℓ : Fin (k + 2) => Fin (n ℓ.val))) (a, f))
          else 0) =
        if a = i then (if (f 0).val = p.val then pathProd T k f * T k a (f (Fin.last k)) else 0)
          else 0 := by
      intro a f
      have e : (Fin.snocEquiv (fun ℓ : Fin (k + 2) => Fin (n ℓ.val))) (a, f) =
          Fin.snoc (α := fun ℓ : Fin (k + 2) => Fin (n ℓ.val)) f a := rfl
      rw [e, snoc_zero', snoc_last', pathProd_snoc]
      by_cases h1 : a = i
      · subst h1; simp
      · have : a.val ≠ i.val := fun h => h1 (Fin.ext h)
        simp [h1, this]
    simp only [key]
    refine Eq.trans ?_ (Fintype.sum_eq_single i (fun b hb => by simp [hb])).symm
    simp only [if_true]
    show ∑ j, T k i j * chain T k j p = _
    simp only [ih, Finset.mul_sum]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun f _ => ?_)
    refine (Fintype.sum_eq_single (f (Fin.last k)) (fun b hb => ?_)).trans ?_
    · have : (f (Fin.last k)).val ≠ b.val := fun h => hb (Fin.ext h).symm
      simp [this]
    · by_cases h : (f 0).val = p.val <;> simp [h, mul_comm]

open MeasureTheory Filter Topology

theorem netZ_cont {n : ℕ → ℕ} {L : ℕ} : ∀ (k : ℕ) (j : Fin (n k)),
    Continuous (fun z : Weights n L × (Fin (n 0) → ℝ) => netZ z.1 z.2 k j)
  | 0, j => by
    show Continuous fun z : Weights n L × (Fin (n 0) → ℝ) => z.2 j
    exact (continuous_apply j).comp continuous_snd
  | k + 1, j => by
    show Continuous fun z : Weights n L × (Fin (n 0) → ℝ) => ∑ m, weight z.1 k j m *
      (if k = 0 then netZ z.1 z.2 k m else relu (netZ z.1 z.2 k m))
    refine continuous_finsetSum _ fun m _ => ?_
    have hw : Continuous fun z : Weights n L × (Fin (n 0) → ℝ) => weight z.1 k j m := by
      unfold weight
      split_ifs with h
      · exact continuous_const.mul ((continuous_apply _).comp continuous_fst)
      · exact continuous_const
    by_cases hk : k = 0
    · simp only [if_pos hk]
      exact hw.mul (netZ_cont k m)
    · simp only [if_neg hk]
      exact hw.mul ((netZ_cont k m).max continuous_const)

noncomputable def act {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) (k : ℕ)
    (m : Fin (n k)) : ℝ :=
  if k = 0 then 1 else if 0 < netZ ω x k m then 1 else 0

noncomputable def TT {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) : ℝ :=
  weight ω ℓ i j * act ω x ℓ j

noncomputable def lin {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) (k : ℕ)
    (y : Fin (n 0) → ℝ) (i : Fin (n k)) : ℝ :=
  ∑ p, chain (TT ω x) k i p * y p

theorem lin_zero {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ)
    (y : Fin (n 0) → ℝ) (i : Fin (n 0)) : lin ω x 0 y i = y i := by
  simp [lin, chain]

theorem lin_succ {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) (k : ℕ)
    (y : Fin (n 0) → ℝ) (i : Fin (n (k + 1))) :
    lin ω x (k + 1) y i = ∑ j, weight ω k i j * (act ω x k j * lin ω x k y j) := by
  simp only [lin, chain, TT, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
  ring

def Good {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) : Prop :=
  ∀ k : ℕ, k < L → ∀ j : Fin (n (k + 1)), netZ ω x (k + 1) j = 0 →
    (k ≠ 0 ∧ ∀ m : Fin (n k), netZ ω x k m ≤ 0)

theorem local_lin {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ)
    (hG : Good ω x) : ∀ k, k ≤ L + 1 →
      ∀ᶠ y in 𝓝 x, ∀ i, netZ ω y k i = lin ω x k y i := by
  intro k
  induction k with
  | zero =>
    intro _
    exact Eventually.of_forall fun y i => by rw [lin_zero]; rfl
  | succ k ih =>
    intro hk
    have hc : ∀ m : Fin (n k), Continuous fun y : Fin (n 0) → ℝ => netZ ω y k m :=
      fun m => (netZ_cont (L := L) k m).comp (continuous_const.prodMk continuous_id)
    have hs : ∀ᶠ y in 𝓝 x, ∀ m : Fin (n k),
        (0 < netZ ω x k m → 0 < netZ ω y k m) ∧ (netZ ω x k m < 0 → netZ ω y k m < 0) := by
      rw [eventually_all]
      intro m
      refine (Eventually.and ?_ ?_)
      · by_cases h : 0 < netZ ω x k m
        · exact ((hc m).tendsto x).eventually (lt_mem_nhds h) |>.mono fun y hy _ => hy
        · exact Eventually.of_forall fun y h' => absurd h' h
      · by_cases h : netZ ω x k m < 0
        · exact ((hc m).tendsto x).eventually (gt_mem_nhds h) |>.mono fun y hy _ => hy
        · exact Eventually.of_forall fun y h' => absurd h' h
    filter_upwards [ih (by omega), hs] with y hy hsy
    intro i
    rw [lin_succ]
    show ∑ j, weight ω k i j * (if k = 0 then netZ ω y k j else relu (netZ ω y k j)) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    by_cases hk0 : k = 0
    · rw [if_pos hk0, hy j]
      simp [act, hk0]
    · rw [if_neg hk0, hy j]
      rcases lt_trichotomy (netZ ω x k j) 0 with hneg | hzero | hpos
      · have h1 := (hsy j).2 hneg
        rw [hy j] at h1
        have : ¬ (0 < netZ ω x k j) := by linarith
        simp only [act, if_neg hk0, if_neg this, relu]
        rw [max_eq_right h1.le]; ring
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨hk'0, hle⟩ := hG k' (by omega) j hzero
        have hl : lin ω x (k' + 1) y j = 0 := by
          rw [lin_succ]
          refine Finset.sum_eq_zero fun m _ => ?_
          have : ¬ (0 < netZ ω x k' m) := not_lt.mpr (hle m)
          simp [act, hk'0, this]
        rw [hl]; simp [relu]
      · have h1 := (hsy j).1 hpos
        rw [hy j] at h1
        simp only [act, if_neg hk0, if_pos hpos, relu]
        rw [max_eq_left h1.le]; ring

theorem update_ne_of_layer_ne {n : ℕ → ℕ} {L : ℕ} {ℓ k : Fin (L + 1)} (h : ℓ.val ≠ k.val)
    (i : Fin (n (ℓ.val + 1))) (j : Fin (n ℓ.val)) (i' : Fin (n (k.val + 1))) (j' : Fin (n k.val)) :
    (⟨ℓ, (i, j)⟩ : WeightIndex n L) ≠ ⟨k, (i', j')⟩ := by
  intro heq
  apply h
  have := congrArg (fun s : WeightIndex n L => s.1.val) heq
  simpa using this

theorem netZ_update_low {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ)
    (i0 : WeightIndex n L) (t : ℝ) :
    ∀ ℓ, ℓ ≤ i0.1.val → netZ (Function.update ω i0 t) x ℓ = netZ ω x ℓ := by
  intro ℓ
  induction ℓ with
  | zero => intro _; rfl
  | succ ℓ ih =>
    intro hℓ
    funext i
    show ∑ j, weight (Function.update ω i0 t) ℓ i j *
        (if ℓ = 0 then netZ (Function.update ω i0 t) x ℓ j
          else relu (netZ (Function.update ω i0 t) x ℓ j)) =
      ∑ j, weight ω ℓ i j * (if ℓ = 0 then netZ ω x ℓ j else relu (netZ ω x ℓ j))
    rw [ih (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    unfold weight
    split_ifs with h
    · congr 1
      apply Function.update_of_ne
      obtain ⟨k, i', j'⟩ := i0
      exact update_ne_of_layer_ne (ℓ := ⟨ℓ, h⟩) (k := k) (by simp at hℓ ⊢; omega) i j i' j'
    · rfl

theorem ae_ne_zero_of_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : ∀ t, μ {t} = 0) (i0 : ι) (f a : (ι → ℝ) → ℝ)
    (hf : Measurable f) (ha : Measurable a)
    (ha_upd : ∀ ω t, a (Function.update ω i0 t) = a ω)
    (hf_upd : ∀ ω t, f (Function.update ω i0 t) = f (Function.update ω i0 0) + a ω * t) :
    ∀ᵐ ω ∂(Measure.pi fun _ : ι => μ), a ω ≠ 0 → f ω ≠ 0 := by
  set S : Set (ι → ℝ) := a ⁻¹' {0}ᶜ ∩ f ⁻¹' {0} with hSdef
  have hS : MeasurableSet S :=
    (ha (measurableSet_singleton (0:ℝ)).compl).inter (hf (measurableSet_singleton 0))
  have hSnull : (Measure.pi fun _ : ι => μ) S = 0 := by
    rw [← lintegral_indicator_one hS,
      lintegral_eq_lmarginal_univ (μ := fun _ : ι => μ) (0 : ι → ℝ),
      lmarginal_erase' (S.indicator 1) (measurable_const.indicator hS) (Finset.mem_univ i0)]
    have hz : (fun x : ι → ℝ => ∫⁻ t, S.indicator 1 (Function.update x i0 t) ∂μ) = 0 := by
      funext x
      have hle : ∀ t, S.indicator (1 : (ι → ℝ) → ENNReal) (Function.update x i0 t) ≤
          ({-(f (Function.update x i0 0)) / a x} : Set ℝ).indicator 1 t := by
        intro t
        by_cases hmem : Function.update x i0 t ∈ S
        · have h1 : a x ≠ 0 := by
            have := hmem.1; simpa [ha_upd] using this
          have h2 : f (Function.update x i0 t) = 0 := hmem.2
          rw [hf_upd] at h2
          have ht : t = -(f (Function.update x i0 0)) / a x := by
            field_simp; linarith
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (by simp [ht])]; simp
        · rw [Set.indicator_of_notMem hmem]; exact zero_le
      refine le_antisymm ?_ zero_le
      calc ∫⁻ t, S.indicator 1 (Function.update x i0 t) ∂μ
          ≤ ∫⁻ t, ({-(f (Function.update x i0 0)) / a x} : Set ℝ).indicator 1 t ∂μ :=
            lintegral_mono hle
        _ = 0 := by
            rw [lintegral_indicator_one (measurableSet_singleton _), hμ]
    rw [hz]
    simp [lmarginal]
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hSnull
  by_contra hn
  apply hω
  intro h1 h2
  exact hn ⟨h1, h2⟩

theorem weight_update_split {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (k : ℕ) (hk : k < L + 1)
    (j : Fin (n (k + 1))) (m : Fin (n k)) (s : ℝ) (m' : Fin (n k)) :
    weight (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ s) k j m' =
      weight (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ 0) k j m' +
        if m' = m then Real.sqrt (2 / (n k : ℝ)) * s else 0 := by
  unfold weight
  rw [dif_pos hk, dif_pos hk]
  by_cases hm : m' = m
  · subst hm; simp
  · have hne : (⟨⟨k, hk⟩, (j, m')⟩ : WeightIndex n L) ≠ ⟨⟨k, hk⟩, (j, m)⟩ := by
      intro h; apply hm; simpa using h
    simp [hm]

theorem netZ_affine {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) (k : ℕ)
    (hk : k < L + 1) (j : Fin (n (k + 1))) (m : Fin (n k)) (t : ℝ) :
    netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ t) x (k + 1) j =
      netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ 0) x (k + 1) j +
        (Real.sqrt (2 / (n k : ℝ)) *
          (if k = 0 then netZ ω x k m else relu (netZ ω x k m))) * t := by
  have hlow : ∀ s : ℝ, netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ s) x k = netZ ω x k :=
    fun s => netZ_update_low ω x _ s k (le_refl k)
  show ∑ m', weight (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ t) k j m' *
      (if k = 0 then netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ t) x k m'
        else relu (netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ t) x k m')) =
    ∑ m', weight (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ 0) k j m' *
      (if k = 0 then netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ 0) x k m'
        else relu (netZ (Function.update ω ⟨⟨k, hk⟩, (j, m)⟩ 0) x k m')) + _
  rw [hlow t, hlow 0]
  rw [Finset.sum_congr rfl fun m' _ => by rw [weight_update_split ω k hk j m t m']]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem good_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ t, μ {t} = 0) (L : ℕ)
    (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ) (x : Fin (n 0) → ℝ) (hx : x ≠ 0) :
    ∀ᵐ ω ∂(weightLaw n L μ), Good ω x := by
  unfold Good weightLaw
  rw [ae_all_iff]; intro k
  by_cases hkL : k < L
  swap
  · exact Eventually.of_forall fun ω h => absurd h hkL
  have hk : k < L + 1 := by omega
  have hsq : 0 < Real.sqrt (2 / (n k : ℝ)) :=
    Real.sqrt_pos.2 (div_pos two_pos (by exact_mod_cast hn k (by omega)))
  have hcω : ∀ (k' : ℕ) (j' : Fin (n k')), Continuous fun ω : Weights n L => netZ ω x k' j' :=
    fun k' j' => (netZ_cont k' j').comp (continuous_id.prodMk continuous_const)
  have base : ∀ (j : Fin (n (k + 1))) (m : Fin (n k)),
      ∀ᵐ ω ∂(Measure.pi fun _ : WeightIndex n L => μ),
        (Real.sqrt (2 / (n k : ℝ)) * (if k = 0 then netZ ω x k m else relu (netZ ω x k m))) ≠ 0 →
          netZ ω x (k + 1) j ≠ 0 := by
    intro j m
    refine ae_ne_zero_of_affine μ hμ ⟨⟨k, hk⟩, (j, m)⟩ (fun ω => netZ ω x (k + 1) j)
      (fun ω => Real.sqrt (2 / (n k : ℝ)) *
        (if k = 0 then netZ ω x k m else relu (netZ ω x k m))) ?_ ?_ ?_ ?_
    · exact (hcω (k + 1) j).measurable
    · by_cases hk0 : k = 0
      · simp only [if_pos hk0]
        exact (continuous_const.mul (hcω k m)).measurable
      · simp only [if_neg hk0]
        exact (continuous_const.mul ((hcω k m).max continuous_const)).measurable
    · intro ω t
      simp only [netZ_update_low ω x ⟨⟨k, hk⟩, (j, m)⟩ t k (le_refl k)]
    · intro ω t
      exact netZ_affine ω x k hk j m t
  have hae : ∀ᵐ ω ∂(Measure.pi fun _ : WeightIndex n L => μ), ∀ j : Fin (n (k + 1)),
      netZ ω x (k + 1) j = 0 → (k ≠ 0 ∧ ∀ m : Fin (n k), netZ ω x k m ≤ 0) := by
    rw [ae_all_iff]; intro j
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨m0, hm0⟩ : ∃ m, x m ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx (funext hcon)
      filter_upwards [base j m0] with ω h hz
      exfalso
      refine h ?_ hz
      rw [if_pos rfl]
      exact mul_ne_zero hsq.ne' hm0
    · have hall : ∀ᵐ ω ∂(Measure.pi fun _ : WeightIndex n L => μ), ∀ m : Fin (n k),
          (Real.sqrt (2 / (n k : ℝ)) *
            (if k = 0 then netZ ω x k m else relu (netZ ω x k m))) ≠ 0 →
          netZ ω x (k + 1) j ≠ 0 := ae_all_iff.2 (base j)
      filter_upwards [hall] with ω h hz
      refine ⟨hk0, fun m => ?_⟩
      by_contra hpos
      push Not at hpos
      refine h m ?_ hz
      rw [if_neg hk0]
      refine mul_ne_zero hsq.ne' ?_
      simp only [relu, max_eq_left hpos.le]
      exact hpos.ne'
  filter_upwards [hae] with ω h _
  exact h

theorem path_match {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ)
    (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    chain (TT ω x) (L + 1) q p =
      ∑ γ ∈ pathsFromTo n L p q, pathWeight ω γ * pathActivation ω x γ := by
  classical
  rw [chain_eq_sum]
  unfold pathsFromTo
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have hc : ((γ 0).val = p.val ∧ (γ (Fin.last (L + 1))).val = q.val) ↔
      (γ 0 = p ∧ γ (Fin.last (L + 1)) = q) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Fin.ext h1, Fin.ext h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1], by rw [h2]⟩
  refine if_congr hc ?_ rfl
  unfold pathProd TT pathWeight pathActivation
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fin.prod_univ_succ]
  have h0 : act ω x ((0 : Fin (L + 1)).val) (γ (Fin.castSucc 0)) = 1 := by simp [act]
  rw [h0, one_mul]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  show (if ℓ.val + 1 = 0 then (1:ℝ) else
    if 0 < netZ ω x (ℓ.val + 1) (γ ⟨ℓ.val + 1, by omega⟩) then 1 else 0) = _
  rw [if_neg (Nat.succ_ne_zero _)]

end PV5d
end LesHouchesWidth

open MeasureTheory ProbabilityTheory LesHouchesWidth Filter Topology in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    ∀ᵐ ω ∂(weightLaw n L μ), jacobianEntry ω x p q =
      ∑ γ ∈ pathsFromTo n L p q, pathWeight ω γ * pathActivation ω x γ := by
  have hμ : ∀ t, μ {t} = 0 := fun t => hμ_ac (by simp)
  filter_upwards [PV5d.good_ae μ hμ L n hn x hx] with ω hG
  have hev := PV5d.local_lin ω x hG (L + 1) le_rfl
  have heq : (fun y => output ω y q) =ᶠ[𝓝 x]
      (fun y : Fin (n 0) → ℝ => ∑ p', PV5d.chain (PV5d.TT ω x) (L + 1) q p' * y p') :=
    hev.mono fun y hy => hy q
  have hd : HasFDerivAt
      (fun y : Fin (n 0) → ℝ => ∑ p', PV5d.chain (PV5d.TT ω x) (L + 1) q p' * y p')
      (∑ p', PV5d.chain (PV5d.TT ω x) (L + 1) q p' •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n 0) => ℝ) p') x := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun p' _ =>
      (hasFDerivAt_apply (𝕜 := ℝ) p' x).const_mul (PV5d.chain (PV5d.TT ω x) (L + 1) q p'))
    simpa using this
  unfold jacobianEntry
  rw [heq.fderiv_eq, hd.fderiv, ← PV5d.path_match]
  simp [Pi.single_apply]
