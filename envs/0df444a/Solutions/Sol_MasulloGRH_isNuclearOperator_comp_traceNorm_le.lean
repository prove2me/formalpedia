-- Prove2me | solution 1 for MasulloGRH.isNuclearOperator_comp_traceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:40:17.349462+00:00
-- url     : https://prove2.me/submissions/67df5343-501c-4f9b-a360-fcc4d033887c

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series
import Theorems.Thm_MasulloGRH_nuclear_trace_hasSum_hilbertBasis

open Filter Topology MeasureTheory
set_option autoImplicit false

namespace Sol_MasulloGRH_isNuclearOperator_comp_traceNorm_le

open MasulloGRH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `‖A x‖ ≤ ‖T x‖` for all `x`, then `A = S ∘ T` for a contraction `S`. -/
theorem exists_contraction_comp_eq (T A : H →L[ℂ] H) (h : ∀ x, ‖A x‖ ≤ ‖T x‖) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ 1 ∧ S.comp T = A := by
  let K := (LinearMap.range (T : H →ₗ[ℂ] H)).topologicalClosure
  let e : H →ₗ[ℂ] K := (T : H →ₗ[ℂ] H).codRestrict K fun x ↦
    (LinearMap.range (T : H →ₗ[ℂ] H)).le_topologicalClosure (LinearMap.mem_range_self _ x)
  have he : DenseRange e := by
    apply Topology.IsInducing.subtypeVal.dense_iff.mpr
    intro x
    rw [← Set.range_comp]
    exact x.property
  have hbound (x : H) : ‖(A : H →ₗ[ℂ] H) x‖ ≤ 1 * ‖e x‖ := by
    rw [one_mul, ← Submodule.norm_coe]
    exact h x
  let S := (A : H →ₗ[ℂ] H).extendOfNorm e
  refine ⟨S.comp K.orthogonalProjectionOnto, ?_, ?_⟩
  · calc
      _ ≤ ‖S‖ * ‖K.orthogonalProjectionOnto‖ := S.opNorm_comp_le _
      _ ≤ 1 * 1 := mul_le_mul (LinearMap.opNorm_extendOfNorm_le he zero_le_one hbound)
        K.orthogonalProjectionOnto_norm_le (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · ext x
    change S (K.orthogonalProjectionOnto (e x : H)) = A x
    rw [K.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact LinearMap.extendOfNorm_eq he ⟨1, hbound⟩ x

theorem star_mul_self_nonneg' (T : H →L[ℂ] H) : 0 ≤ star T * T :=
  star_mul_self_nonneg T

theorem operatorAbs_nonneg (T : H →L[ℂ] H) : 0 ≤ operatorAbs T := CFC.sqrt_nonneg _

/-- `‖|T| x‖ = ‖T x‖`. -/
theorem norm_operatorAbs_apply (T : H →L[ℂ] H) (x : H) : ‖operatorAbs T x‖ = ‖T x‖ := by
  set S := operatorAbs T with hSdef
  have hS : S.adjoint = S := (IsSelfAdjoint.of_nonneg (operatorAbs_nonneg T)).adjoint_eq
  have hsq : S * S = star T * T := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg' T)
  have hsq' : S.adjoint.comp S = T.adjoint.comp T := by rw [hS]; exact hsq
  rw [S.apply_norm_eq_sqrt_inner_adjoint_right, T.apply_norm_eq_sqrt_inner_adjoint_right, hsq']

omit [CompleteSpace H] in
/-- Reindexing a rank-one expansion over an arbitrary index type by `ℕ`. -/
theorem exists_nat_expansion {ι : Type*} (T : H →L[ℂ] H) (f g : ι → H) (c : ℝ)
    (hc : HasSum (fun i => ‖f i‖ * ‖g i‖) c)
    (hT : ∀ u, HasSum (fun i => inner ℂ (f i) u • g i) (T u)) :
    ∃ x y : ℕ → H, HasSum (fun m => ‖x m‖ * ‖y m‖) c ∧
      ∀ u, HasSum (fun m => inner ℂ (x m) u • y m) (T u) := by
  classical
  set I := Function.support (fun i => ‖f i‖ * ‖g i‖) with hIdef
  have hI : I.Countable := hc.summable.countable_support
  have : Countable I := hI.to_subtype
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  let φ : I → H × H := fun i => (f i.1, g i.1)
  let p : ℕ → H × H := Function.extend e φ 0
  refine ⟨fun m => (p m).1, fun m => (p m).2, ?_, ?_⟩
  · have h1 : HasSum (fun i : I => ‖f i.1‖ * ‖g i.1‖) c :=
      (hasSum_subtype_iff_of_support_subset (subset_refl _)).mpr hc
    have h2 := (hasSum_extend_zero he).mpr h1
    have hfun : (fun m => ‖(p m).1‖ * ‖(p m).2‖) =
        Function.extend e (fun i : I => ‖f i.1‖ * ‖g i.1‖) 0 := by
      funext m
      have h := Function.apply_extend (g := φ) (fun a : H × H => ‖a.1‖ * ‖a.2‖) e 0 m
      have h0 : ((fun a : H × H => ‖a.1‖ * ‖a.2‖) ∘ (0 : ℕ → H × H)) = 0 := by
        funext n; simp
      rw [h0] at h
      exact h
    rw [hfun]
    exact h2
  · intro u
    have hsupp : Function.support (fun i => inner ℂ (f i) u • g i) ⊆ I := by
      intro i hi
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact hi (by simp [norm_eq_zero.mp h])
      · exact hi (by simp [norm_eq_zero.mp h])
    have h1 : HasSum (fun i : I => inner ℂ (f i.1) u • g i.1) (T u) :=
      (hasSum_subtype_iff_of_support_subset hsupp).mpr (hT u)
    have h2 := (hasSum_extend_zero he).mpr h1
    have hfun : (fun m => inner ℂ (p m).1 u • (p m).2) =
        Function.extend e (fun i : I => inner ℂ (f i.1) u • g i.1) 0 := by
      funext m
      have h := Function.apply_extend (g := φ) (fun a : H × H => inner ℂ a.1 u • a.2) e 0 m
      have h0 : ((fun a : H × H => inner ℂ a.1 u • a.2) ∘ (0 : ℕ → H × H)) = 0 := by
        funext n; simp
      rw [h0] at h
      exact h
    rw [hfun]
    exact h2

/-- A nuclear operator has a rank-one expansion whose cost is at most its trace norm. -/
theorem exists_expansion_le_traceNorm (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    ∃ x y : ℕ → H, Summable (fun m => ‖x m‖ * ‖y m‖) ∧
      (∀ u, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) ∧
      ∑' m, ‖x m‖ * ‖y m‖ ≤ traceNorm T := by
  set S := operatorAbs T with hSdef
  have hS0 : 0 ≤ S := operatorAbs_nonneg T
  set B := CFC.sqrt S with hBdef
  have hB0 : 0 ≤ B := CFC.sqrt_nonneg S
  have hBadj : B.adjoint = B := (IsSelfAdjoint.of_nonneg hB0).adjoint_eq
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBBu (u : H) : B (B u) = S u := by rw [← hBB]; rfl
  obtain ⟨V, -, hV⟩ := exists_contraction_comp_eq T S (fun x => (norm_operatorAbs_apply T x).le)
  obtain ⟨W, hW, hWS⟩ := exists_contraction_comp_eq S T (fun x => (norm_operatorAbs_apply T x).ge)
  -- `|T| = V T` is nuclear
  have hSnuc : IsNuclearOperator S := by
    obtain ⟨x, y, hs, hxy⟩ := hT
    refine ⟨x, fun m => V (y m), ?_, fun u => ?_⟩
    · refine (hs.mul_left ‖V‖).of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      calc ‖x m‖ * ‖V (y m)‖ ≤ ‖x m‖ * (‖V‖ * ‖y m‖) :=
            mul_le_mul_of_nonneg_left (V.le_opNorm _) (norm_nonneg _)
        _ = ‖V‖ * (‖x m‖ * ‖y m‖) := by ring
    · have h1 := V.hasSum (hxy u)
      have h2 : V (T u) = S u := by rw [← hV]; rfl
      rw [h2] at h1
      simpa only [map_smul] using h1
  let b := chosenHilbertBasis H
  have hdiag := (nuclear_trace_hasSum_hilbertBasis S hSnuc b).2
  have hterm (i) : (inner ℂ (b i) (S (b i))).re = ‖B (b i)‖ ^ 2 := by
    rw [← hBBu, ← ContinuousLinearMap.adjoint_inner_left, hBadj, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hre : HasSum (fun i => ‖B (b i)‖ ^ 2) (traceNorm T) := by
    have := Complex.hasSum_re hdiag
    simp only [hterm] at this
    exact this
  have hexp (u : H) : HasSum (fun i => inner ℂ (B (b i)) u • W (B (b i))) (T u) := by
    have h1 := (W.comp B).hasSum (b.hasSum_repr (B u))
    have h2 : (W.comp B) (B u) = T u := by
      change W (B (B u)) = T u
      rw [hBBu, ← hWS]; rfl
    rw [h2] at h1
    convert h1 using 1
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply, ← ContinuousLinearMap.adjoint_inner_left, hBadj]
    rfl
  have hcost_le (i) : ‖B (b i)‖ * ‖W (B (b i))‖ ≤ ‖B (b i)‖ ^ 2 := by
    have : ‖W (B (b i))‖ ≤ ‖B (b i)‖ :=
      (W.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hW)
    nlinarith [norm_nonneg (B (b i))]
  have hcost_sum : Summable (fun i => ‖B (b i)‖ * ‖W (B (b i))‖) :=
    hre.summable.of_nonneg_of_le (fun i => by positivity) hcost_le
  obtain ⟨x, y, hxy_cost, hxy⟩ :=
    exists_nat_expansion T (fun i => B (b i)) (fun i => W (B (b i))) _ hcost_sum.hasSum hexp
  refine ⟨x, y, hxy_cost.summable, hxy, ?_⟩
  rw [hxy_cost.tsum_eq]
  exact hasSum_le hcost_le hcost_sum.hasSum hre

end Sol_MasulloGRH_isNuclearOperator_comp_traceNorm_le

open MasulloGRH Sol_MasulloGRH_isNuclearOperator_comp_traceNorm_le in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) (A : H →L[ℂ] H) :
    IsNuclearOperator (A ∘L T) ∧ IsNuclearOperator (T ∘L A) ∧
      traceNorm (A ∘L T) ≤ ‖A‖ * traceNorm T ∧
      traceNorm (T ∘L A) ≤ ‖A‖ * traceNorm T := by
  obtain ⟨x, y, hs, hxy, hle⟩ := exists_expansion_le_traceNorm T hT
  have hL : ∀ u, HasSum (fun m => inner ℂ (x m) u • A (y m)) ((A ∘L T) u) := fun u => by
    simpa only [map_smul, ContinuousLinearMap.comp_apply] using A.hasSum (hxy u)
  have hR : ∀ u, HasSum (fun m => inner ℂ (A.adjoint (x m)) u • y m) ((T ∘L A) u) := fun u => by
    simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply] using
      hxy (A u)
  have hLc : ∀ m, ‖x m‖ * ‖A (y m)‖ ≤ ‖A‖ * (‖x m‖ * ‖y m‖) := fun m => by
    calc ‖x m‖ * ‖A (y m)‖ ≤ ‖x m‖ * (‖A‖ * ‖y m‖) :=
          mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ * (‖x m‖ * ‖y m‖) := by ring
  have hRc : ∀ m, ‖A.adjoint (x m)‖ * ‖y m‖ ≤ ‖A‖ * (‖x m‖ * ‖y m‖) := fun m => by
    have hadj : ‖A.adjoint‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ A
    calc ‖A.adjoint (x m)‖ * ‖y m‖ ≤ (‖A.adjoint‖ * ‖x m‖) * ‖y m‖ :=
          mul_le_mul_of_nonneg_right (A.adjoint.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ * (‖x m‖ * ‖y m‖) := by rw [hadj]; ring
  have hLs : Summable (fun m => ‖x m‖ * ‖A (y m)‖) :=
    (hs.mul_left ‖A‖).of_nonneg_of_le (fun m => by positivity) hLc
  have hRs : Summable (fun m => ‖A.adjoint (x m)‖ * ‖y m‖) :=
    (hs.mul_left ‖A‖).of_nonneg_of_le (fun m => by positivity) hRc
  refine ⟨⟨x, fun m => A (y m), hLs, hL⟩, ⟨fun m => A.adjoint (x m), y, hRs, hR⟩, ?_, ?_⟩
  · calc traceNorm (A ∘L T) ≤ ∑' m, ‖x m‖ * ‖A (y m)‖ :=
          traceNorm_le_nuclear_series _ _ _ hLs hL
      _ ≤ ∑' m, ‖A‖ * (‖x m‖ * ‖y m‖) := hLs.tsum_le_tsum hLc (hs.mul_left _)
      _ = ‖A‖ * ∑' m, ‖x m‖ * ‖y m‖ := tsum_mul_left
      _ ≤ ‖A‖ * traceNorm T := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  · calc traceNorm (T ∘L A) ≤ ∑' m, ‖A.adjoint (x m)‖ * ‖y m‖ :=
          traceNorm_le_nuclear_series _ _ _ hRs hR
      _ ≤ ∑' m, ‖A‖ * (‖x m‖ * ‖y m‖) := hRs.tsum_le_tsum hRc (hs.mul_left _)
      _ = ‖A‖ * ∑' m, ‖x m‖ * ‖y m‖ := tsum_mul_left
      _ ≤ ‖A‖ * traceNorm T := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
