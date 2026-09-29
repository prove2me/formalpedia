-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fe7b92d5-b8fc-54f5-a576-f2ea8356da56

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical

namespace B2dLattice

theorem one_add_mul_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 1 + t * ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + t * a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ha' : ∀ i ∈ s, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hj0 : 0 ≤ a j := ha j (Finset.mem_insert_self j s)
    have hP : 1 ≤ ∏ i ∈ s, (1 + t * a i) :=
      Finset.one_le_prod fun i hi => le_add_of_nonneg_right (mul_nonneg ht (ha' i hi))
    have h1 := ih ha'
    have : 0 ≤ t * a j := mul_nonneg ht hj0
    nlinarith [mul_nonneg this (sub_nonneg.mpr hP)]

variable (F : Type) [Field F] [NumberField F]

theorem norm_le_sum_coords (x : mixedSpace F) :
    ‖x‖ ≤ (∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ := by
  have h1 : ‖x.1‖ ≤ ∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun w _ => abs_nonneg _)).mpr fun w => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun w => |x.1 w|) (fun w _ => abs_nonneg _) (Finset.mem_univ w)
  have h2 : ‖x.2‖ ≤ ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun w _ => norm_nonneg _)).mpr fun w => ?_
    exact Finset.single_le_sum (f := fun w => ‖x.2 w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ w)
  rw [Prod.norm_def]
  refine max_le (h1.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => norm_nonneg _)))
    (h2.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun w _ => abs_nonneg _)))

theorem normAtPlace_le_norm (w : InfinitePlace F) (x : mixedSpace F) : normAtPlace w x ≤ ‖x‖ := by
  by_cases hw : w.IsReal
  · rw [normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm _ _).trans (le_max_left _ _)
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
    exact (norm_le_pi_norm _ _).trans (le_max_right _ _)

theorem abs_norm_le_norm_pow (ξ : F) :
    ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) ≤ ‖mixedEmbedding F ξ‖ ^ Module.finrank ℚ F := by
  rw [← norm_eq_norm, mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg _ _) _) fun w _ => ?_
  exact pow_le_pow_left₀ (normAtPlace_nonneg _ _) (normAtPlace_le_norm F w _) _

theorem weight_le (N : ℕ) (t : ℝ) (ht : 0 < t) (x : mixedSpace F) (hx : x ≠ 0) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |x.1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖x.2 w‖) ^ (-(2 * N : ℝ))
      ≤ (t * ‖x‖) ^ (-(N : ℝ)) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx

  have hc : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (1 + t * ‖x.2 w‖) ^ (-(2 * N : ℝ)) ≤ (1 + t * ‖x.2 w‖) ^ (-(N : ℝ)) := fun w =>
    Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) (by
      have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith)
  have step1 : (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |x.1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖x.2 w‖) ^ (-(2 * N : ℝ))
      ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |x.1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖x.2 w‖) ^ (-(N : ℝ)) := by
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun w _ => by positivity) fun w _ => hc w)
      (Finset.prod_nonneg fun w _ => by positivity)
  refine step1.trans ?_
  rw [Real.finset_prod_rpow _ _ (fun w _ => by positivity), Real.finset_prod_rpow _ _ (fun w _ => by positivity),
    ← Real.mul_rpow (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity)]

  refine Real.rpow_le_rpow_of_nonpos (mul_pos ht hxn) ?_ (by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith)
  have hsum := norm_le_sum_coords F x
  have hP1 := one_add_mul_sum_le_prod (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}) (fun w => |x.1 w|) t ht.le
    (fun w _ => abs_nonneg _)
  have hP2 := one_add_mul_sum_le_prod (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}) (fun w => ‖x.2 w‖) t ht.le
    (fun w _ => norm_nonneg _)
  have hA : 0 ≤ ∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w| := Finset.sum_nonneg fun w _ => abs_nonneg _
  have hB : 0 ≤ ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ := Finset.sum_nonneg fun w _ => norm_nonneg _
  calc t * ‖x‖ ≤ t * ((∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖) :=
        mul_le_mul_of_nonneg_left hsum ht.le
    _ ≤ (1 + t * ∑ w : {w : InfinitePlace F // w.IsReal}, |x.1 w|) * (1 + t * ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖) := by
        nlinarith [mul_nonneg ht.le hA, mul_nonneg ht.le hB, mul_nonneg (mul_nonneg ht.le hA) (mul_nonneg ht.le hB)]
    _ ≤ _ := mul_le_mul hP1 hP2 (by positivity) ((Finset.prod_nonneg fun w _ => by positivity))

theorem exists_pos_forall_le_norm {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ L, x ≠ 0 → δ ≤ ‖x‖ := by
  have h0 : IsOpen ({0} : Set L) := isOpen_discrete _
  rw [Metric.isOpen_iff] at h0
  obtain ⟨ε, hε, hball⟩ := h0 0 (Set.mem_singleton 0)
  refine ⟨ε, hε, fun x hx hx0 => ?_⟩
  by_contra hlt
  push_neg at hlt
  have : (⟨x, hx⟩ : L) ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hlt
  have h := hball this
  rw [Set.mem_singleton_iff] at h
  exact hx0 (congrArg Subtype.val h)

end B2dLattice

open B2dLattice in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (k N' : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} =>
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))) ∧
      ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I},
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))
        ≤ C * t ^ (-(N' : ℝ)) := by
  set n : ℕ := Module.finrank ℚ F with hn
  by_cases hI : I = 0
  · haveI : IsEmpty {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} := ⟨fun ξ => ξ.2.1 (by
      have h : (ξ.1 : F) ∈ (0 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := hI ▸ ξ.2.2
      exact (FractionalIdeal.mem_zero_iff _).mp h)⟩
    refine ⟨0, fun N _ => ⟨0, fun t _ => ⟨(hasSum_empty).summable, ?_⟩⟩⟩
    rw [tsum_empty, zero_mul]

  set Iu : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 I hI with hIu
  set L : Submodule ℤ (mixedSpace F) := mixedEmbedding.idealLattice F Iu with hL
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_forall_le_norm L
  have hrank : Module.finrank ℤ L = n := by rw [ZLattice.rank ℝ L, mixedEmbedding.finrank]
  refine ⟨n * k + n + N' + 1, fun N hN => ?_⟩

  set p : ℝ := (N : ℝ) - n * k with hp
  have hNr : ((n * k + n + N' + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hNr
  have hpn : -p < -(Module.finrank ℤ L : ℝ) := by rw [hrank, hp]; linarith
  have hS := ZLattice.summable_norm_rpow L (-p) hpn
  set S : ℝ := ∑' x : L, ‖x‖ ^ (-p) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _

  set cδ : ℝ := max 1 (δ⁻¹ ^ n) with hcδ
  have hcδ1 : 1 ≤ cδ := le_max_left _ _
  set K₀ : ℝ := cδ ^ k * t₀ ^ (-((N : ℝ) - N')) with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (pow_nonneg (zero_le_one.trans hcδ1) _) (Real.rpow_nonneg ht₀.le _)
  refine ⟨K₀ * S, fun t ht => ?_⟩
  have ht0 : 0 < t := ht₀.trans_le ht

  let ι : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} → L := fun ξ =>
    ⟨mixedEmbedding F ξ.1, (mixedEmbedding.mem_idealLattice F Iu).mpr ⟨ξ.1, ξ.2.2, rfl⟩⟩
  have hι : Function.Injective ι := by
    intro a b hab
    have h := congrArg (fun z : L => (z : mixedSpace F)) hab
    exact Subtype.ext ((mixedEmbedding_injective F) h)
  have hιne : ∀ ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, (ι ξ : mixedSpace F) ≠ 0 := fun ξ h =>
    ξ.2.1 ((map_eq_zero_iff _ (mixedEmbedding_injective F)).mp h)
  have hιδ : ∀ ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, δ ≤ ‖(ι ξ : mixedSpace F)‖ := fun ξ =>
    hδ _ (ι ξ).2 (hιne ξ)

  set term : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} → ℝ := fun ξ =>
    (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
      (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ)) with hterm
  have hnn : ∀ ξ, 0 ≤ term ξ := fun ξ => by
    simp only [hterm]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (Finset.prod_nonneg fun w _ => by positivity))
      (Finset.prod_nonneg fun w _ => by positivity)

  have hpt : ∀ ξ, term ξ ≤ K₀ * t ^ (-(N' : ℝ)) * ‖(ι ξ : mixedSpace F)‖ ^ (-p) := by
    intro ξ
    set x : mixedSpace F := (ι ξ : mixedSpace F) with hxdef
    have hxmE : x = mixedEmbedding F ξ.1 := rfl
    have hxδ : δ ≤ ‖x‖ := hιδ ξ
    have hx0 : 0 < ‖x‖ := hδ0.trans_le hxδ

    have hA : (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k ≤ cδ ^ k * ‖x‖ ^ (n * k) := by
      have h1 : max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ) ≤ cδ * ‖x‖ ^ n := by
        refine max_le ?_ ((abs_norm_le_norm_pow F ξ.1).trans ?_)
        ·
          have : 1 ≤ (δ⁻¹ * ‖x‖) ^ n := one_le_pow₀ (by rw [inv_mul_eq_div, le_div_iff₀ hδ0]; simpa using hxδ)
          rw [mul_pow] at this
          exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (norm_nonneg _) _))
        · rw [← hxmE]
          exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg _) _) hcδ1
      calc (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k ≤ (cδ * ‖x‖ ^ n) ^ k :=
            pow_le_pow_left₀ (by positivity) h1 k
        _ = cδ ^ k * ‖x‖ ^ (n * k) := by rw [mul_pow, ← pow_mul]

    have hB := weight_le F N t ht0 x (hιne ξ)

    have hC : (t * ‖x‖) ^ (-(N : ℝ)) ≤ t ^ (-(N' : ℝ)) * t₀ ^ (-((N : ℝ) - N')) * ‖x‖ ^ (-(N : ℝ)) := by
      rw [Real.mul_rpow ht0.le (norm_nonneg _)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
      have hsplit : t ^ (-(N : ℝ)) = t ^ (-(N' : ℝ)) * t ^ (-((N : ℝ) - N')) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht0.le _)
      have hnk : (0 : ℝ) ≤ (n : ℝ) * k := by positivity
      exact Real.rpow_le_rpow_of_nonpos ht₀ ht (by linarith)

    have hW : (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))
        ≤ t ^ (-(N' : ℝ)) * t₀ ^ (-((N : ℝ) - N')) * ‖x‖ ^ (-(N : ℝ)) := by
      rw [← hxmE]; exact hB.trans hC
    have hWnn : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ)) :=
      mul_nonneg (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity)
    calc term ξ = (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          ((∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
            ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))) := by
          simp only [hterm, mul_assoc]
      _ ≤ (cδ ^ k * ‖x‖ ^ (n * k)) * (t ^ (-(N' : ℝ)) * t₀ ^ (-((N : ℝ) - N')) * ‖x‖ ^ (-(N : ℝ))) :=
          mul_le_mul hA hW hWnn (by positivity)
      _ = K₀ * t ^ (-(N' : ℝ)) * (‖x‖ ^ (n * k) * ‖x‖ ^ (-(N : ℝ))) := by simp only [hK₀]; ring
      _ = K₀ * t ^ (-(N' : ℝ)) * ‖x‖ ^ (-p) := by
          rw [← Real.rpow_natCast ‖x‖ (n * k), ← Real.rpow_add hx0]
          congr 2
          push_cast
          simp only [hp]; ring

  have hmajS : Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} => ‖(ι ξ : mixedSpace F)‖ ^ (-p)) := by
    have := hS.comp_injective hι
    exact this
  have hmaj : Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} => K₀ * t ^ (-(N' : ℝ)) * ‖(ι ξ : mixedSpace F)‖ ^ (-p)) :=
    hmajS.mul_left _
  have hsum : Summable term := Summable.of_nonneg_of_le hnn hpt hmaj
  refine ⟨by simpa only [hterm] using hsum, ?_⟩
  have hle : ∑' ξ, term ξ ≤ K₀ * S * t ^ (-(N' : ℝ)) := by
    calc ∑' ξ, term ξ ≤ ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, K₀ * t ^ (-(N' : ℝ)) * ‖(ι ξ : mixedSpace F)‖ ^ (-p) :=
          hsum.tsum_le_tsum hpt hmaj
      _ = K₀ * t ^ (-(N' : ℝ)) * ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I}, ‖(ι ξ : mixedSpace F)‖ ^ (-p) := tsum_mul_left
      _ ≤ K₀ * t ^ (-(N' : ℝ)) * S := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK₀0 (Real.rpow_nonneg ht0.le _))
          have hcmp := tsum_comp_le_tsum_of_inj (f := fun x : L => ‖x‖ ^ (-p)) hS
            (fun x => Real.rpow_nonneg (norm_nonneg _) _) hι
          exact hcmp
      _ = K₀ * S * t ^ (-(N' : ℝ)) := mul_right_comm _ _ _
  simpa only [hterm] using hle

end S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg (solution)
