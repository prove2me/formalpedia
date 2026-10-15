-- Prove2me | solution 1 for OAI.HoneycombForce.logPartition_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:32:04.660458+00:00
-- url     : https://prove2.me/submissions/2c357b79-c5ac-483e-805e-c4ce9e7460bf

-- Generated from openai/math@1581d4c lean/OAI/Probability/Honeycomb/FreeEnergy.lean:L716-L718
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.HoneycombForce.logPartition_tendsto.
-- The statement is the platform stub (Theorems.Thm_OAI_HoneycombForce_logPartition_tendsto) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_HoneycombFreeEnergy
import Definitions.Def_OAI_Probability_Honeycomb_FreeEnergy
import Theorems.Thm_OAI_HoneycombForce_partition_split

-- ---- inline helpers from OAI.Probability.Honeycomb.FreeEnergy ----
namespace OAI

/-! Forced honeycomb walks and existence of their fixed-length free energy. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

theorem mem_neighbors_iff (v w : Vertex) : w ∈ neighbors v ↔ Adj v w := by
  rcases v with ⟨i, j, s⟩
  rcases w with ⟨k, l, t⟩
  cases s <;> cases t <;>
    simp [neighbors, Adj, UpDownAdj, up, down, Vertex.mk.injEq] <;> omega

theorem mem_walkLists_iff (o : Vertex) (n : ℕ) (γ : List Vertex) :
    γ ∈ walkLists o n ↔
      γ.head? = some o ∧ γ.length = n + 1 ∧ γ.IsChain Adj := by
  induction n generalizing o γ with
  | zero =>
      cases γ with
      | nil => simp [walkLists]
      | cons v vs =>
          cases vs with
          | nil => simp [walkLists, eq_comm]
          | cons w ws => simp [walkLists]
  | succ n ih =>
      simp only [walkLists, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, xs, hxs, rfl⟩
        obtain ⟨hh, hl, hc⟩ := (ih v xs).mp hxs
        cases xs with
        | nil => simp at hh
        | cons w ws =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst w
            exact ⟨rfl, by simpa using congrArg Nat.succ hl,
              List.isChain_cons_cons.mpr ⟨(mem_neighbors_iff o v).mp hv, hc⟩⟩
      · rintro ⟨hh, hl, hc⟩
        cases γ with
        | nil => simp at hh
        | cons v vs =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst v
            cases vs with
            | nil => simp at hl
            | cons w ws =>
                obtain ⟨how, hws⟩ := List.isChain_cons_cons.mp hc
                refine ⟨w, (mem_neighbors_iff o w).mpr how, w :: ws, ?_, rfl⟩
                apply (ih w (w :: ws)).mpr
                exact ⟨rfl, by simpa using Nat.succ.inj hl, hws⟩

theorem mem_saws_iff (o : Vertex) (n : ℕ) (γ : List Vertex) :
    γ ∈ saws o n ↔ γ.head? = some o ∧ γ.length = n + 1 ∧
      γ.IsChain Adj ∧ γ.Nodup := by
  simp only [saws, Finset.mem_filter, mem_walkLists_iff]
  tauto

theorem rho_pos : 0 < rho := by
  unfold rho
  positivity

theorem rho_nonneg : 0 ≤ rho := rho_pos.le

theorem partition_nonneg (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    0 ≤ partition o e s n := by
  apply Finset.sum_nonneg
  intro γ _
  exact mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le

theorem shiftVertex_injective (i j : ℤ) : Function.Injective (shiftVertex i j) := by
  intro v w h
  have hc := congrArg Vertex.col h
  have hr := congrArg Vertex.row h
  have hu := congrArg Vertex.up h
  cases v; cases w
  simp only [shiftVertex, Vertex.mk.injEq] at hc hr hu ⊢
  exact ⟨add_right_cancel hc, add_right_cancel hr, hu⟩

theorem rowVertex_injective : Function.Injective rowVertex := by
  intro k l h
  have hc := congrArg Vertex.col h
  have hs := congrArg Vertex.up h
  by_cases hk : k % 2 = 0 <;> by_cases hl : l % 2 = 0 <;>
    simp [rowVertex, hk, hl, up, down] at hc hs <;> omega

theorem rowVertex_adj (k : ℕ) : Adj (rowVertex k) (rowVertex (k+1)) := by
  by_cases hk : k % 2 = 0
  · have hk' : (k+1) % 2 ≠ 0 := by omega
    have he : (k+1) / 2 = k / 2 := by omega
    simp [rowVertex, hk, hk', Adj, UpDownAdj, up, down, he]
  · have hk' : (k+1) % 2 = 0 := by omega
    have he : (k+1) / 2 = k / 2 + 1 := by omega
    simp [rowVertex, hk, hk', Adj, UpDownAdj, up, down, he]

theorem ray_injective (o : Vertex) : Function.Injective (ray o) :=
  (shiftVertex_injective _ _).comp (rowVertex_injective.comp
    (fun _ _ h => Nat.add_right_cancel h))

theorem ray_adj (o : Vertex) (k : ℕ) : Adj (ray o k) (ray o (k+1)) := by
  simp only [ray, shiftVertex_adj]
  rw [show k + 1 + (if o.up then 0 else 1) = (k + if o.up then 0 else 1) + 1 by omega]
  exact rowVertex_adj _

theorem rayPath_mem (o : Vertex) (n : ℕ) : rayPath o n ∈ saws o n := by
  unfold rayPath
  apply (mem_saws_iff _ _ _).mpr
  refine ⟨?_, by simp, ?_, ?_⟩
  · rw [List.head?_eq_getElem?]
    simp
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_ofFn]
    exact ray_adj o i
  · exact List.nodup_ofFn.mpr ((ray_injective o).comp Fin.val_injective)

theorem saws_nonempty (o : Vertex) (n : ℕ) : (saws o n).Nonempty :=
  ⟨rayPath o n, rayPath_mem o n⟩

theorem partition_pos (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    0 < partition o e s n := by
  obtain ⟨γ, hγ⟩ := saws_nonempty o n
  apply lt_of_lt_of_le (mul_pos (pow_pos rho_pos n) (Real.exp_pos _))
  exact Finset.single_le_sum
    (fun γ _ => mul_nonneg (pow_nonneg rho_nonneg n) (Real.exp_pos _).le) hγ

theorem position_shift (i j : ℤ) (v : Vertex) :
    position (shiftVertex i j v) = position v +
      (⟨(i : ℝ) + (j : ℝ) / 2, rowSpacing * (j : ℝ)⟩ : ℂ) := by
  rcases v with ⟨a, b, u⟩
  cases u <;> apply Complex.ext <;> simp [position, shiftVertex] <;> ring

theorem displacement_shift (i j : ℤ) (o : Vertex) (γ : List Vertex) :
    displacement (shiftVertex i j o) (γ.map (shiftVertex i j)) = displacement o γ := by
  unfold displacement endpoint
  rw [List.getLastD_map, position_shift, position_shift]
  abel

theorem mem_saws_shift {o : Vertex} {n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o n) (i j : ℤ) :
    γ.map (shiftVertex i j) ∈ saws (shiftVertex i j o) n := by
  obtain ⟨hh, hl, hc, hn⟩ := (mem_saws_iff _ _ _).mp hγ
  apply (mem_saws_iff _ _ _).mpr
  refine ⟨by simp [hh], by simpa using hl, ?_, ?_⟩
  · apply List.isChain_map_of_isChain _ _ hc
    intro v w hvw
    exact (shiftVertex_adj i j v w).mpr hvw
  · exact (List.nodup_map_iff (shiftVertex_injective i j)).mpr hn

theorem saws_shift (o : Vertex) (n : ℕ) (i j : ℤ) :
    saws (shiftVertex i j o) n = (saws o n).image (List.map (shiftVertex i j)) := by
  ext γ
  constructor
  · intro hγ
    refine Finset.mem_image.mpr ⟨γ.map (shiftVertex (-i) (-j)), ?_, ?_⟩
    · simpa using mem_saws_shift hγ (-i) (-j)
    · simp [List.map_map, Function.comp_def]
  · rintro hγ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hγ
    exact mem_saws_shift hη i j

theorem partition_shift (o : Vertex) (n : ℕ) (i j : ℤ) (e : ℂ) (s : ℝ) :
    partition (shiftVertex i j o) e s n = partition o e s n := by
  unfold partition
  rw [saws_shift, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro γ _
    rw [displacement_shift]
  · exact fun _ _ _ _ h =>
      (List.map_injective_iff.mpr (shiftVertex_injective i j)) h

theorem partition_eq_base (o : Vertex) (n : ℕ) (e : ℂ) (s : ℝ) :
    partition o e s n = partition (baseVertex o.up) e s n := by
  convert partition_shift (baseVertex o.up) n o.col o.row e s using 1
  cases o
  simp [baseVertex, shiftVertex]

theorem partition_le_maxPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition o e s n ≤ maxPartition e s n := by
  rw [partition_eq_base]
  cases o.up
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem maxPartition_pos (e : ℂ) (s : ℝ) (n : ℕ) : 0 < maxPartition e s n :=
  (partition_pos (baseVertex true) e s n).trans_le (le_max_left _ _)

theorem partition_le_mul_maxPartition (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) :
    partition o e s (n+m) ≤ partition o e s n * maxPartition e s m := by
  apply (partition_split o e s n m).trans
  rw [partition, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left (partition_le_maxPartition _ e s m)
    (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)

theorem maxPartition_submultiplicative (e : ℂ) (s : ℝ) (n m : ℕ) :
    maxPartition e s (n+m) ≤ maxPartition e s n * maxPartition e s m := by
  apply max_le
  · exact (partition_le_mul_maxPartition _ e s n m).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (maxPartition_pos _ _ _).le)
  · exact (partition_le_mul_maxPartition _ e s n m).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (maxPartition_pos _ _ _).le)

theorem maxPartition_log_subadditive (e : ℂ) (s : ℝ) :
    Subadditive (fun n => Real.log (maxPartition e s n)) := by
  intro n m
  calc
    Real.log (maxPartition e s (n+m)) ≤
        Real.log (maxPartition e s n * maxPartition e s m) :=
      Real.log_le_log (maxPartition_pos _ _ _) (maxPartition_submultiplicative _ _ _ _)
    _ = _ := Real.log_mul (maxPartition_pos _ _ _).ne' (maxPartition_pos _ _ _).ne'

theorem endpoint_one_type {o : Vertex} {γ : List Vertex} (hγ : γ ∈ saws o 1) :
    (endpoint o γ).up = !o.up := by
  have hh := (Finset.mem_filter.mp hγ).1
  simp only [walkLists, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_singleton] at hh
  obtain ⟨v, hv, _, rfl, rfl⟩ := hh
  have hav := (mem_neighbors_iff o v).mp hv
  rcases hav with ⟨ho, hv, _⟩ | ⟨hv, ho, _⟩ <;> simp [endpoint, ho, hv]

theorem partition_succ_opposite (u : Bool) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition (baseVertex u) e s (n+1) ≤
      partition (baseVertex u) e s 1 * partition (baseVertex (!u)) e s n := by
  rw [Nat.add_comm n 1]
  apply (partition_split (baseVertex u) e s 1 n).trans_eq
  conv_rhs => rw [partition, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [partition_eq_base (endpoint _ _), endpoint_one_type hγ]
  rfl

theorem maxPartition_succ_le (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    maxPartition e s (n+1) ≤ maxPartition e s 1 * partition o e s n := by
  have same (u : Bool) : partition (baseVertex u) e s (n+1) ≤
      maxPartition e s 1 * partition (baseVertex u) e s n := by
    simpa only [mul_comm] using partition_le_mul_maxPartition (baseVertex u) e s n 1
  have opposite (u : Bool) : partition (baseVertex (!u)) e s (n+1) ≤
      maxPartition e s 1 * partition (baseVertex u) e s n := by
    simpa only [Bool.not_not] using (partition_succ_opposite (!u) e s n).trans
      (mul_le_mul_of_nonneg_right (partition_le_maxPartition _ e s 1)
        (partition_nonneg _ e s n))
  rw [partition_eq_base o]
  cases o.up
  · exact max_le (opposite false) (same false)
  · exact max_le (same true) (opposite true)

theorem position_rowVertex (n : ℕ) :
    position (rowVertex n) - position (baseVertex true) =
      (⟨(n : ℝ) / 2, if n % 2 = 0 then 0 else rowSpacing / 3⟩ : ℂ) := by
  by_cases hn : n % 2 = 0
  · have hn' : (n / 2 : ℕ) * 2 = n := by omega
    have hr : ((n / 2 : ℕ) : ℝ) * 2 = n := by exact_mod_cast hn'
    apply Complex.ext <;> simp [rowVertex, hn, position, up, baseVertex, -Int.natCast_ediv]
    linarith
  · have hn' : (n / 2 : ℕ) * 2 + 1 = n := by omega
    have hr : ((n / 2 : ℕ) : ℝ) * 2 + 1 = n := by exact_mod_cast hn'
    apply Complex.ext <;> simp [rowVertex, hn, position, down, baseVertex, -Int.natCast_ediv] <;> linarith

theorem rowPath_projection_lower (e : ℂ) (s : ℝ) {n : ℕ} (hn : 0 < n) :
    -(n : ℝ) * rowCost e s ≤
      s * projection e (displacement (baseVertex true) (rayPath (baseVertex true) n)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hx := mul_le_mul_of_nonneg_left (neg_abs_le (s * e.re / 2)) hn0
  have hy := neg_abs_le (s * e.im * rowSpacing / 3)
  have hy' := mul_le_mul_of_nonneg_right hnr (abs_nonneg (s * e.im * rowSpacing / 3))
  simp only [displacement, endpoint_rayPath, ray, baseVertex,
    ↓reduceIte, Nat.add_zero, shiftVertex_zero]
  rw [show (⟨0, 0, true⟩ : Vertex) = baseVertex true from rfl, position_rowVertex]
  by_cases hp : n % 2 = 0 <;>
    simp [projection, rowCost, hp, Complex.mul_re] <;>
    nlinarith [abs_nonneg (s * e.im * rowSpacing / 3)]

theorem maxPartition_log_linear_lower (e : ℂ) (s : ℝ) (n : ℕ) :
    (n : ℝ) * (Real.log rho - rowCost e s) ≤ Real.log (maxPartition e s n) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hw : rho ^ n * Real.exp (s * projection e
      (displacement (baseVertex true) (rayPath (baseVertex true) n))) ≤
      maxPartition e s n := by
    apply le_trans _ (partition_le_maxPartition (baseVertex true) e s n)
    unfold partition
    apply Finset.single_le_sum
      (f := fun γ => rho ^ n * Real.exp (s * projection e (displacement (baseVertex true) γ)))
      (a := rayPath (baseVertex true) n)
    · intro γ _
      exact mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le
    · exact rayPath_mem (baseVertex true) n
  apply le_trans _ (Real.log_le_log (mul_pos (pow_pos rho_pos _) (Real.exp_pos _)) hw)
  rw [Real.log_mul (pow_pos rho_pos _).ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp]
  have hp := rowPath_projection_lower e s (Nat.pos_of_ne_zero hn)
  linarith

theorem maxPartition_log_div_bddBelow (e : ℂ) (s : ℝ) :
    BddBelow (Set.range (fun n : ℕ => Real.log (maxPartition e s n) / (n : ℝ))) := by
  refine ⟨min 0 (Real.log rho - rowCost e s), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp
  · apply (min_le_right _ _).trans
    apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    simpa only [mul_comm] using maxPartition_log_linear_lower e s n

theorem exists_logPartition_limit (o : Vertex) (e : ℂ) (s : ℝ) :
    ∃ f : ℝ, Tendsto (logPartition o e s) atTop (𝓝 f) := by
  let hsub := maxPartition_log_subadditive e s
  have hlim := hsub.tendsto_lim (maxPartition_log_div_bddBelow e s)
  refine ⟨hsub.lim, ?_⟩
  have hshift := hlim.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1 (d := 1) one_ne_zero)
  have hlower : Tendsto (fun n : ℕ =>
      (Real.log (maxPartition e s (n+1)) - Real.log (maxPartition e s 1)) / (n : ℝ))
      atTop (𝓝 hsub.lim) := by
    have h := (hshift.mul hratio).sub
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (maxPartition e s 1)))
    simp only [mul_one, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [Function.comp_def]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hlim
  · filter_upwards with n
    have hlog := Real.log_le_log (maxPartition_pos e s (n+1))
      (maxPartition_succ_le o e s n)
    rw [Real.log_mul (maxPartition_pos e s 1).ne' (partition_pos o e s n).ne'] at hlog
    exact div_le_div_of_nonneg_right (by linarith :
      Real.log (maxPartition e s (n+1)) - Real.log (maxPartition e s 1) ≤
        Real.log (partition o e s n)) (Nat.cast_nonneg _)
  · filter_upwards with n
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (partition_pos o e s n) (partition_le_maxPartition o e s n))
      (Nat.cast_nonneg _)

end HoneycombForce

end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.HoneycombForce
open scoped ENNReal Topology
open Filter

theorem solution (o : Vertex) (e : ℂ) (s : ℝ) :
    Tendsto (logPartition o e s) atTop (𝓝 (freeEnergy o e s)) :=
  tendsto_nhds_limUnder (exists_logPartition_limit o e s)
