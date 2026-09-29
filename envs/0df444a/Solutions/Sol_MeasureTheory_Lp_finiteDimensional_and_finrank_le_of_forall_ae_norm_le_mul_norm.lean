-- Prove2me | solution 1 for MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/385aea5f-49e9-53c1-b63b-3607dd3c4704

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace GodementAux

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {𝕜 : Type*} [RCLike 𝕜]

theorem coeFn_finset_sum {ι : Type*} {p : ℝ≥0∞} (s : Finset ι) (f : ι → Lp 𝕜 p μ) :
    (((∑ i ∈ s, f i : Lp 𝕜 p μ) : X → 𝕜)) =ᵐ[μ] fun x => ∑ i ∈ s, (f i : X → 𝕜) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
    exact hx
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx hix
    rw [hx, Pi.add_apply, hix]

theorem norm_sq_eq_integral (φ : Lp 𝕜 2 μ) : ‖φ‖ ^ 2 = ∫ x, ‖(φ : X → 𝕜) x‖ ^ 2 ∂μ := by
  rw [← @inner_self_eq_norm_sq 𝕜, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  have : (fun a => ((‖(φ : X → 𝕜) a‖ : 𝕜) ^ 2)) = fun a => (((‖(φ : X → 𝕜) a‖ ^ 2 : ℝ)) : 𝕜) := by
    funext a; push_cast; rfl
  rw [this, integral_ofReal, RCLike.ofReal_re]

theorem integrable_norm_sq (φ : Lp 𝕜 2 μ) : Integrable (fun x => ‖(φ : X → 𝕜) x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp φ).1).mp (Lp.memLp φ)

theorem card_le_of_orthonormal [IsFiniteMeasure μ] (C : ℝ) {m : ℕ} (e : Fin m → Lp 𝕜 2 μ) (he : Orthonormal 𝕜 e)
    (hb : ∀ c : Fin m → 𝕜, ∀ᵐ x ∂μ, ‖((∑ i, c i • e i : Lp 𝕜 2 μ) : X → 𝕜) x‖ ≤ C * ‖∑ i, c i • e i‖) :
    (m : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by

  have hnorm : ∀ c : EuclideanSpace 𝕜 (Fin m), ‖∑ i, c i • e i‖ = ‖c‖ := by
    intro c
    have h1 : ‖∑ i, c i • e i‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq 𝕜, he.inner_sum, EuclideanSpace.norm_sq_eq, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.conj_mul]; norm_cast
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace 𝕜 (Fin m))
  have hae : ∀ᵐ x ∂μ, ∀ k, ‖∑ i, u k i * (e i : X → 𝕜) x‖ ≤ C * ‖u k‖ := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hb (u k), coeFn_finset_sum Finset.univ (fun i => u k i • e i),
      ae_all_iff.mpr fun i => Lp.coeFn_smul (u k i) (e i)] with x hx hsum hsmul
    rw [hnorm] at hx
    rw [hsum] at hx
    simp only [hsmul, Pi.smul_apply, smul_eq_mul] at hx
    exact hx

  have hall : ∀ᵐ x ∂μ, ∀ c : EuclideanSpace 𝕜 (Fin m), ‖∑ i, c i * (e i : X → 𝕜) x‖ ≤ C * ‖c‖ := by
    filter_upwards [hae] with x hx
    have hclosed : IsClosed {c : EuclideanSpace 𝕜 (Fin m) | ‖∑ i, c i * (e i : X → 𝕜) x‖ ≤ C * ‖c‖} := by
      refine isClosed_le ?_ (by fun_prop)
      refine Continuous.norm (continuous_finsetSum _ fun i _ => ?_)
      exact (PiLp.continuous_apply 2 _ i).mul continuous_const
    intro c
    have hc : c ∈ closure (Set.range u) := by rw [hu.closure_range]; exact Set.mem_univ c
    exact hclosed.closure_subset_iff.mpr (Set.range_subset_iff.mpr hx) hc

  set s : X → ℝ := fun x => ∑ i, ‖(e i : X → 𝕜) x‖ ^ 2 with hs_def
  have hs_nonneg : ∀ x, 0 ≤ s x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs : ∀ᵐ x ∂μ, s x ≤ C ^ 2 := by
    filter_upwards [hall] with x hx
    let c : EuclideanSpace 𝕜 (Fin m) := WithLp.toLp 2 fun i => conj ((e i : X → 𝕜) x)
    have hcx : ∑ i, c i * (e i : X → 𝕜) x = ((s x : ℝ) : 𝕜) := by
      simp only [hs_def, c]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact RCLike.conj_mul _
    have hcn : ‖c‖ = Real.sqrt (s x) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c]
    have h := hx c
    rw [hcx, hcn, RCLike.norm_ofReal, abs_of_nonneg (hs_nonneg x)] at h

    by_cases h0 : s x = 0
    · rw [h0]; exact sq_nonneg C
    · have hpos : 0 < Real.sqrt (s x) := Real.sqrt_pos.mpr (lt_of_le_of_ne (hs_nonneg x) (Ne.symm h0))
      have hsq : Real.sqrt (s x) * Real.sqrt (s x) = s x := Real.mul_self_sqrt (hs_nonneg x)
      have hle : Real.sqrt (s x) ≤ C := by
        have : Real.sqrt (s x) * Real.sqrt (s x) ≤ C * Real.sqrt (s x) := by rw [hsq]; exact h
        exact le_of_mul_le_mul_right this hpos
      calc s x = Real.sqrt (s x) ^ 2 := by rw [sq, hsq]
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

  have hint : Integrable s μ := integrable_finsetSum _ fun i _ => integrable_norm_sq (e i)
  have h1 : ∫ x, s x ∂μ = m := by
    simp only [hs_def]
    rw [integral_finsetSum _ fun i _ => integrable_norm_sq (e i)]
    simp_rw [← norm_sq_eq_integral, he.norm_eq_one]
    simp
  have h2 : ∫ x, s x ∂μ ≤ ∫ _x, C ^ 2 ∂μ := integral_mono_ae hint (integrable_const _) hs
  rw [h1, integral_const, smul_eq_mul, measureReal_def] at h2
  linarith

end GodementAux

open GodementAux in

theorem solution
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by

  set N : ℕ := ⌊C ^ 2 * (μ Set.univ).toReal⌋₊ with hN
  have hNN : (0 : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := mul_nonneg (sq_nonneg C) ENNReal.toReal_nonneg
  have key : ∀ s : Finset V, (LinearIndependent 𝕜 fun i : s => (i : V)) → s.card ≤ N := by
    intro s hs

    have hs' : LinearIndependent 𝕜 fun i : s => ((i : V) : Lp 𝕜 2 μ) :=
      hs.map' V.subtype (Submodule.ker_subtype V)
    set W : Submodule 𝕜 (Lp 𝕜 2 μ) := Submodule.span 𝕜 (Set.range fun i : s => ((i : V) : Lp 𝕜 2 μ)) with hW
    have hWV : W ≤ V := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (i : V).2
    haveI : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
    have hfr : Module.finrank 𝕜 W = s.card := by
      rw [hW, finrank_span_eq_card hs']; simp

    let b := stdOrthonormalBasis 𝕜 W
    let e : Fin (Module.finrank 𝕜 W) → Lp 𝕜 2 μ := fun i => (b i : Lp 𝕜 2 μ)
    have he : Orthonormal 𝕜 e := (W.subtypeₗᵢ.orthonormal_comp_iff).mpr b.orthonormal
    have hmem : ∀ c : Fin (Module.finrank 𝕜 W) → 𝕜, (∑ i, c i • e i : Lp 𝕜 2 μ) ∈ V :=
      fun c => V.sum_mem fun i _ => V.smul_mem _ (hWV (b i).2)
    have hle := card_le_of_orthonormal C e he fun c => hV _ (hmem c)
    rw [hfr] at hle
    exact Nat.le_floor hle
  have hrank : Module.rank 𝕜 V ≤ N := rank_le key
  have hfin : Module.Finite 𝕜 V := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := N))
  refine ⟨hfin, ?_⟩
  calc (Module.finrank 𝕜 V : ℝ) ≤ N := by exact_mod_cast Module.finrank_le_of_rank_le hrank
    _ ≤ C ^ 2 * (μ Set.univ).toReal := Nat.floor_le hNN

end S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
end P2MW
export P2MW.S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm (solution)
