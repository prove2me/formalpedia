-- Prove2me | solution 1 for MasulloGRH.completedProjTensor_exists_series
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:49:57.356406+00:00
-- url     : https://prove2.me/submissions/bf3dcb08-4609-4779-a171-55696a4d8473

import Definitions.Def_TopologicalTensorProduct_Completion
import Theorems.Thm_MasulloGRH_projTensor_nhds_zero_hasBasis

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_completedProjTensor_exists_series

open MasulloGRH Set
open scoped ComplexOrder Pointwise

section algebraic

/-- A balanced convex set containing `0` is stable under the combinations `∑ a k • w k` with
`∑ ‖a k‖ ≤ 1`. -/
theorem sum_smul_mem {X : Type*} [AddCommGroup X] [Module ℂ X] {T : Set X}
    (hb : Balanced ℂ T) (hc : Convex ℂ T) (h0 : (0 : X) ∈ T)
    {κ : Type*} (t : Finset κ) (a : κ → ℂ) (w : κ → X)
    (hw : ∀ k ∈ t, w k ∈ T) (ha : ∑ k ∈ t, ‖a k‖ ≤ 1) : ∑ k ∈ t, a k • w k ∈ T := by
  classical
  have hcR : Convex ℝ T := convex_RCLike_iff_convex_real.1 hc
  have hR0 : 0 ≤ ∑ k ∈ t, ‖a k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  rcases hR0.eq_or_lt with hz | hpos
  · have h1 : ∀ k ∈ t, a k = 0 := fun k hk => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => norm_nonneg (a k))).1 hz.symm k hk
      simpa using this
    rw [Finset.sum_eq_zero (fun k hk => by rw [h1 k hk, zero_smul])]
    exact h0
  · set R : ℝ := ∑ k ∈ t, ‖a k‖ with hR
    have key : ∑ k ∈ t, (‖a k‖ / R) • ((a k / (‖a k‖ : ℂ)) • w k) ∈ T := by
      refine hcR.sum_mem (fun k _ => div_nonneg (norm_nonneg _) hR0) ?_ (fun k hk => ?_)
      · rw [← Finset.sum_div, div_self hpos.ne']
      · refine hb.smul_mem ?_ (hw k hk)
        rw [norm_div, Complex.norm_real, norm_norm]
        exact div_self_le_one _
    have h2 : ∑ k ∈ t, a k • w k
        = (R : ℂ) • ∑ k ∈ t, (‖a k‖ / R) • ((a k / (‖a k‖ : ℂ)) • w k) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.coe_smul, smul_smul, smul_smul]
      congr 1
      by_cases hk : a k = 0
      · simp [hk]
      · have hk' : (‖a k‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hk).ne'
        have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        push_cast
        field_simp
    rw [h2]
    exact hb.smul_mem (by rw [Complex.norm_real, Real.norm_of_nonneg hR0]; exact ha) key

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- Every element of the convex circled hull of `(ε U) ⊗ V` is a finite combination
`∑ a j • x j ⊗ y j` with `x j ∈ U`, `y j ∈ V` and `∑ ‖a j‖ ≤ ε`. -/
theorem exists_rep (U : Set E) (V : Set F) (ε : ℝ) (hε : 0 < ε) (v : E ⊗[ℂ] F)
    (hv : v ∈ absConvexHull ℂ (image2 (fun x y => x ⊗ₜ[ℂ] y) ((ε : ℂ) • U) V)) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (x : ι → E) (y : ι → F),
      (∀ j, x j ∈ U) ∧ (∀ j, y j ∈ V) ∧ ∑ j, ‖a j‖ ≤ ε ∧ v = ∑ j, a j • x j ⊗ₜ[ℂ] y j := by
  let R : Set (E ⊗[ℂ] F) := {v | ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (x : ι → E) (y : ι → F),
      (∀ j, x j ∈ U) ∧ (∀ j, y j ∈ V) ∧ ∑ j, ‖a j‖ ≤ ε ∧ v = ∑ j, a j • x j ⊗ₜ[ℂ] y j}
  have hsub : image2 (fun x y => x ⊗ₜ[ℂ] y) ((ε : ℂ) • U) V ⊆ R := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩
    refine ⟨Unit, inferInstance, fun _ => (ε : ℂ), fun _ => x, fun _ => y, fun _ => hx,
      fun _ => hy, ?_, ?_⟩
    · simp [abs_of_pos hε]
    · simp [TensorProduct.smul_tmul']
  have hbal : Balanced ℂ R := by
    rw [balanced_iff_smul_mem]
    rintro c hc _ ⟨ι, _, a, x, y, hx, hy, ha, rfl⟩
    refine ⟨ι, inferInstance, fun j => c * a j, x, y, hx, hy, ?_, ?_⟩
    · calc ∑ j, ‖c * a j‖ = ‖c‖ * ∑ j, ‖a j‖ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => norm_mul _ _
        _ ≤ 1 * ε := mul_le_mul hc ha (Finset.sum_nonneg fun j _ => norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  have hconv : Convex ℂ R := by
    rintro _ ⟨ι, _, a, x, y, hx, hy, ha, rfl⟩ _ ⟨ι', _, a', x', y', hx', hy', ha', rfl⟩
      α β hα hβ hαβ
    have hnorm : ‖α‖ + ‖β‖ = 1 := by
      have h1 := Complex.eq_coe_norm_of_nonneg hα
      have h2 := Complex.eq_coe_norm_of_nonneg hβ
      have h3 : ((‖α‖ + ‖β‖ : ℝ) : ℂ) = 1 := by
        push_cast
        rw [← h1, ← h2, hαβ]
      exact_mod_cast h3
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim (fun j => α * a j) (fun j => β * a' j),
      Sum.elim x x', Sum.elim y y', ?_, ?_, ?_, ?_⟩
    · rintro (j | j)
      · exact hx j
      · exact hx' j
    · rintro (j | j)
      · exact hy j
      · exact hy' j
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, norm_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      calc ‖α‖ * ∑ j, ‖a j‖ + ‖β‖ * ∑ j, ‖a' j‖ ≤ ‖α‖ * ε + ‖β‖ * ε :=
            add_le_add (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
              (mul_le_mul_of_nonneg_left ha' (norm_nonneg _))
        _ = ε := by rw [← add_mul, hnorm, one_mul]
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Finset.smul_sum, Finset.smul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  exact absConvexHull_min hsub ⟨hbal, hconv⟩ hv

/-- Every tensor is a finite sum `∑ a j • x j ⊗ y j` with `∑ ‖a j‖` as small as we wish. -/
theorem exists_rep_any (u : E ⊗[ℂ] F) : ∀ δ : ℝ, 0 < δ →
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (x : ι → E) (y : ι → F),
      ∑ j, ‖a j‖ ≤ δ ∧ u = ∑ j, a j • x j ⊗ₜ[ℂ] y j := by
  induction u using TensorProduct.induction_on with
  | zero =>
    intro δ hδ
    exact ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun _ => 0, by simpa using hδ.le, by simp⟩
  | tmul x y =>
    intro δ hδ
    refine ⟨Unit, inferInstance, fun _ => (δ : ℂ), fun _ => ((δ : ℂ)⁻¹ • x), fun _ => y, ?_, ?_⟩
    · simp [abs_of_pos hδ]
    · have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
      simp [TensorProduct.smul_tmul', smul_smul, hδ']
  | add u u' hu hu' =>
    intro δ hδ
    obtain ⟨ι, _, a, x, y, ha, rfl⟩ := hu (δ / 2) (half_pos hδ)
    obtain ⟨ι', _, a', x', y', ha', rfl⟩ := hu' (δ / 2) (half_pos hδ)
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim x x', Sum.elim y y', ?_, ?_⟩
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      linarith
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]

end algebraic

section reindex

/-- Extending by zero along an injection into `ℕ` turns a cofinite null family into a null
sequence. -/
theorem tendsto_extend_zero {κ : Type*} {α : Type*} [TopologicalSpace α] [Zero α]
    {g : κ → ℕ} (hg : Function.Injective g) {x : κ → α} (hx : Tendsto x cofinite (𝓝 0)) :
    Tendsto (Function.extend g x 0) atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  intro S hS
  have hfin : {k | x k ∉ S}.Finite := by
    have := hx hS
    rwa [mem_map, mem_cofinite] at this
  rw [mem_map, mem_cofinite]
  refine (hfin.image g).subset ?_
  intro n hn
  by_cases h : ∃ k, g k = n
  · obtain ⟨k, rfl⟩ := h
    refine ⟨k, ?_, rfl⟩
    intro hk
    apply hn
    show Function.extend g x 0 (g k) ∈ S
    rw [hg.extend_apply]
    exact hk
  · exfalso
    apply hn
    show Function.extend g x 0 n ∈ S
    rw [Function.extend_apply' _ _ _ h]
    exact mem_of_mem_nhds hS

end reindex

section main

/-- A finite sum of nonnegative terms over a sigma type with finite fibres is bounded by the sum
of the fibrewise bounds. -/
theorem sum_sigma_le {ι : ℕ → Type} [∀ n, Fintype (ι n)] (f : (Σ n, ι n) → ℝ)
    (hf : ∀ k, 0 ≤ f k) (ε : ℕ → ℝ) (hε : Summable ε) (h : ∀ n, ∑ j, f ⟨n, j⟩ ≤ ε n)
    (t : Finset (Σ n, ι n)) : ∑ k ∈ t, f k ≤ ∑' n, ε n := by
  classical
  have hε0 : ∀ n, 0 ≤ ε n := fun n => (Finset.sum_nonneg fun j _ => hf ⟨n, j⟩).trans (h n)
  calc ∑ k ∈ t, f k ≤ ∑ k ∈ (t.image Sigma.fst).sigma (fun _ => Finset.univ), f k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hf k)
        intro k hk
        rw [Finset.mem_sigma]
        exact ⟨Finset.mem_image_of_mem _ hk, Finset.mem_univ _⟩
    _ = ∑ n ∈ t.image Sigma.fst, ∑ j, f ⟨n, j⟩ := Finset.sum_sigma _ _ _
    _ ≤ ∑ n ∈ t.image Sigma.fst, ε n := Finset.sum_le_sum fun n _ => h n
    _ ≤ ∑' n, ε n := hε.sum_le_tsum _ (fun n _ => hε0 n)

/-- The series representation, indexed by a countable type. -/
theorem exists_family (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsFrechet E) (hF : IsFrechet F)
    (Y : Type v) [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : E ⊗[ℂ] F →ₗ[ℂ] Y) (hi : IsCompletedProjTensor E F i) (z : Y) :
    ∃ (κ : Type) (_ : Countable κ) (c : κ → ℂ) (x : κ → E) (y : κ → F),
      Summable (fun k => ‖c k‖) ∧ Tendsto x cofinite (𝓝 0) ∧ Tendsto y cofinite (𝓝 0) ∧
      HasSum (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) z := by
  classical
  have hE' : IsHLCS E := ⟨hE.1, hE.2.1.1⟩
  have hF' : IsHLCS F := ⟨hF.1, hF.2.1.1⟩
  have hbasis := MasulloGRH.projTensor_nhds_zero_hasBasis E F hE' hF'
  obtain ⟨⟨ιE, _, pE, hpE⟩, -, hEm⟩ := hE
  obtain ⟨⟨ιF, _, pF, hpF⟩, -, hFm⟩ := hF
  have : IsTopologicalAddGroup E := hpE.topologicalAddGroup
  have : ContinuousSMul ℂ E := hpE.continuousSMul
  obtain ⟨⟨⟨ιY, _, pY, hpY⟩, -⟩, -, -, htop, hdense⟩ := hi
  have : IsTopologicalAddGroup Y := hpY.topologicalAddGroup
  -- decreasing countable bases of neighbourhoods of `0` in `E` and `F`
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 (0 : F)).exists_antitone_basis
  -- the weights
  set ε : ℕ → ℝ := fun n => 1 / 2 / 2 ^ n with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n => by
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [hε]
    simp only
    rw [div_le_one (by positivity)]
    linarith
  have hεsum : Summable ε := summable_geometric_two' 1
  have hεtsum : ∑' n, ε n = 1 := tsum_geometric_two' 1
  -- the two neighbourhood sequences in `E ⊗_π F`
  set W : ℕ → Set (E ⊗[ℂ] F) := fun n =>
    absConvexHull ℂ (image2 (fun x y => x ⊗ₜ[ℂ] y) (U n) (V n)) with hW
  set G : ℕ → Set (E ⊗[ℂ] F) := fun n =>
    absConvexHull ℂ (image2 (fun x y => x ⊗ₜ[ℂ] y) ((ε (n + 1) : ℂ) • U n) (V n)) with hG
  have hWbal : ∀ n, Balanced ℂ (W n) := fun n => balanced_absConvexHull
  have hWconv : ∀ n, Convex ℂ (W n) := fun n => convex_absConvexHull
  have htmulW : ∀ n, ∀ x ∈ U n, ∀ y ∈ V n, x ⊗ₜ[ℂ] y ∈ W n := fun n x hx y hy =>
    subset_absConvexHull ⟨x, hx, y, hy, rfl⟩
  have hW0 : ∀ n, (0 : E ⊗[ℂ] F) ∈ W n := fun n =>
    (hWbal n).zero_mem ⟨_, htmulW n 0 (mem_of_mem_nhds (hU.1.mem_of_mem trivial)) 0
      (mem_of_mem_nhds (hV.1.mem_of_mem trivial))⟩
  have hGW : ∀ n, G n ⊆ W n := by
    intro n
    refine absConvexHull_min ?_ ⟨hWbal n, hWconv n⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩
    show ((ε (n + 1) : ℂ) • x) ⊗ₜ[ℂ] y ∈ W n
    rw [← TensorProduct.smul_tmul']
    refine (hWbal n).smul_mem ?_ (htmulW n x hx y hy)
    rw [Complex.norm_real, Real.norm_of_nonneg (hεpos _).le]
    exact hεle _
  have hWanti : ∀ m n, m ≤ n → W n ⊆ W m := fun m n hmn =>
    absConvexHull_mono (image2_subset (hU.2 hmn) (hV.2 hmn))
  have hGnhds : ∀ n, G n ∈ @nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0 := by
    intro n
    refine hbasis.mem_of_mem (i := ((ε (n + 1) : ℂ) • U n, V n)) ⟨?_, hV.1.mem_of_mem trivial⟩
    have hne : (ε (n + 1) : ℂ) ≠ 0 := by exact_mod_cast (hεpos (n + 1)).ne'
    exact (set_smul_mem_nhds_zero_iff hne).2 (hU.1.mem_of_mem trivial)
  -- neighbourhoods of `0` in `Y` pull back to neighbourhoods of `0` in `E ⊗_π F`
  have hpre : ∀ N ∈ 𝓝 (0 : Y), i ⁻¹' N ∈ @nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0 := by
    intro N hN
    rw [htop, nhds_induced, map_zero]
    exact preimage_mem_comap hN
  have hWbase : ∀ N ∈ 𝓝 (0 : Y), ∃ m, i '' W m ⊆ N := by
    intro N hN
    obtain ⟨⟨U₀, V₀⟩, ⟨hU₀, hV₀⟩, hsub⟩ := hbasis.mem_iff.1 (hpre N hN)
    obtain ⟨m₁, -, hm₁⟩ := hU.1.mem_iff.1 hU₀
    obtain ⟨m₂, -, hm₂⟩ := hV.1.mem_iff.1 hV₀
    refine ⟨max m₁ m₂, image_subset_iff.2 (subset_trans ?_ hsub)⟩
    exact absConvexHull_mono (image2_subset ((hU.2 (le_max_left _ _)).trans hm₁)
      ((hV.2 (le_max_right _ _)).trans hm₂))
  -- open neighbourhoods `P n` of `0` in `Y` with `i ⁻¹ (P n - P n) ⊆ G n`
  have hP : ∀ n, ∃ P : Set Y, IsOpen P ∧ (0 : Y) ∈ P ∧
      ∀ a ∈ P, ∀ b ∈ P, ∀ w : E ⊗[ℂ] F, i w = a - b → w ∈ G n := by
    intro n
    have h1 := hGnhds n
    rw [htop, nhds_induced, map_zero, mem_comap] at h1
    obtain ⟨t, ht, hsub⟩ := h1
    have h2 : (fun p : Y × Y => p.1 - p.2) ⁻¹' t ∈ 𝓝 ((0, 0) : Y × Y) := by
      refine (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds ?_
      simpa using ht
    obtain ⟨P, hPo, hP0, hPsub⟩ := exists_nhds_square h2
    refine ⟨P, hPo, hP0, fun a ha b hb w hw => hsub ?_⟩
    show i w ∈ t
    rw [hw]
    exact hPsub (mk_mem_prod ha hb)
  choose P hPo hP0 hPsub using hP
  -- the approximating sequence
  have hu : ∀ n, ∃ w : E ⊗[ℂ] F, i w - z ∈ P n ∧ i w - z ∈ P (n - 1) := by
    intro n
    have hopen : IsOpen ((fun y : Y => y - z) ⁻¹' (P n ∩ P (n - 1))) :=
      ((hPo n).inter (hPo (n - 1))).preimage (continuous_id.sub continuous_const)
    obtain ⟨w, hw⟩ := hdense.exists_mem_open hopen ⟨z, by simp [hP0]⟩
    exact ⟨w, hw.1, hw.2⟩
  choose u hu1 hu2 using hu
  have hstep : ∀ n, u (n + 1) - u n ∈ G n := by
    intro n
    have h1 : i (u (n + 1)) - z ∈ P n := by simpa using hu2 (n + 1)
    refine hPsub n _ h1 _ (hu1 n) _ ?_
    rw [map_sub]
    abel
  have hPcl : ∀ n, P n ⊆ closure (i '' W n) := by
    intro n
    refine (hdense.open_subset_closure_inter (hPo n)).trans (closure_mono ?_)
    rintro _ ⟨hy, w, rfl⟩
    exact ⟨w, hGW n (hPsub n _ hy 0 (hP0 n) w (sub_zero _).symm), rfl⟩
  have hsmall : ∀ N ∈ 𝓝 (0 : Y), ∃ M, P M ⊆ N ∧ i '' W M ⊆ N := by
    intro N hN
    obtain ⟨N₁, hN₁, hN₁c, hN₁N⟩ := exists_mem_nhds_isClosed_subset hN
    obtain ⟨M, hM⟩ := hWbase N₁ hN₁
    exact ⟨M, ((hPcl M).trans (closure_minimal hM hN₁c)).trans hN₁N, hM.trans hN₁N⟩
  -- the blocks
  set D : ℕ → E ⊗[ℂ] F := fun n => Nat.rec (u 0) (fun m _ => u (m + 1) - u m) n with hD
  have hD0 : D 0 = u 0 := rfl
  have hDs : ∀ m, D (m + 1) = u (m + 1) - u m := fun m => rfl
  have hsumD : ∀ M, ∑ n ∈ Finset.range (M + 1), D n = u M := by
    intro M
    induction M with
    | zero => rw [Finset.sum_range_one, hD0]
    | succ M ih => rw [Finset.sum_range_succ, ih, hDs]; abel
  have hblock : ∀ n, ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (x : ι → E) (y : ι → F),
      D n = ∑ j, a j • x j ⊗ₜ[ℂ] y j ∧ ∑ j, ‖a j‖ ≤ ε n ∧
        ∀ m, n = m + 1 → (∀ j, x j ∈ U m) ∧ (∀ j, y j ∈ V m) := by
    intro n
    cases n with
    | zero =>
      obtain ⟨ι, inst, a, x, y, ha, h⟩ := exists_rep_any (u 0) (ε 0) (hεpos 0)
      exact ⟨ι, inst, a, x, y, h, ha, fun m hm => absurd hm (Nat.succ_ne_zero m).symm⟩
    | succ m =>
      obtain ⟨ι, inst, a, x, y, hx, hy, ha, h⟩ :=
        exists_rep (U m) (V m) (ε (m + 1)) (hεpos _) (u (m + 1) - u m) (hstep m)
      refine ⟨ι, inst, a, x, y, h, ha, fun m' hm' => ?_⟩
      obtain rfl : m = m' := Nat.succ_injective hm'
      exact ⟨hx, hy⟩
  choose ι inst a X Yv hDeq hale hmem using hblock
  let _ : ∀ n, Fintype (ι n) := inst
  -- membership of the points of the blocks `≥ M + 1`
  have hXU : ∀ M n, M + 1 ≤ n → ∀ j, X n j ∈ U M ∧ Yv n j ∈ V M := by
    intro M n hn j
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    have hMm : M ≤ m := by omega
    exact ⟨hU.2 hMm ((hmem (m + 1) m rfl).1 j), hV.2 hMm ((hmem (m + 1) m rfl).2 j)⟩
  refine ⟨Σ n, ι n, inferInstance, fun k => a k.1 k.2, fun k => X k.1 k.2,
    fun k => Yv k.1 k.2, ?_, ?_, ?_, ?_⟩
  · -- absolute summability of the coefficients
    refine (summable_sigma_of_nonneg (fun k => norm_nonneg _)).2
      ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun j => norm_nonneg _) (fun n => ?_)
      hεsum
    rw [tsum_fintype]
    exact hale n
  · intro S hS
    obtain ⟨m, -, hm⟩ := hU.1.mem_iff.1 hS
    rw [mem_map, mem_cofinite]
    refine ((Finset.range (m + 1)).sigma (fun n => (Finset.univ : Finset (ι n)))).finite_toSet.subset
      ?_
    rintro ⟨n, j⟩ hk
    rw [Finset.mem_coe, Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_range]
    by_contra hlt
    have hlt' : m + 1 ≤ n := not_lt.1 hlt
    exact hk (hm (hXU m n hlt' j).1)
  · intro S hS
    obtain ⟨m, -, hm⟩ := hV.1.mem_iff.1 hS
    rw [mem_map, mem_cofinite]
    refine ((Finset.range (m + 1)).sigma (fun n => (Finset.univ : Finset (ι n)))).finite_toSet.subset
      ?_
    rintro ⟨n, j⟩ hk
    rw [Finset.mem_coe, Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_range]
    by_contra hlt
    have hlt' : m + 1 ≤ n := not_lt.1 hlt
    exact hk (hm (hXU m n hlt' j).2)
  · -- the sum
    rw [HasSum, SummationFilter.unconditional_filter, tendsto_atTop']
    intro N hN
    have h1 : (fun p : Y × Y => z + p.1 + p.2) ⁻¹' N ∈ 𝓝 ((0, 0) : Y × Y) := by
      refine ((continuous_const.add continuous_fst).add continuous_snd).continuousAt.preimage_mem_nhds
        ?_
      simpa using hN
    obtain ⟨N₁, hN₁o, hN₁0, hN₁sub⟩ := exists_nhds_square h1
    obtain ⟨M, hMP, hMW⟩ := hsmall N₁ (hN₁o.mem_nhds hN₁0)
    set s₀ : Finset (Σ n, ι n) :=
      (Finset.range (M + 1)).sigma (fun n => (Finset.univ : Finset (ι n))) with hs₀
    refine ⟨s₀, fun s hs => ?_⟩
    have hhead : ∑ k ∈ s₀, a k.1 k.2 • i (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2) = i (u M) := by
      rw [hs₀, Finset.sum_sigma, ← hsumD M, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hDeq n, map_sum]
      exact Finset.sum_congr rfl fun j _ => (map_smul i _ _).symm
    have htail : ∑ k ∈ s \ s₀, a k.1 k.2 • i (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2) ∈ N₁ := by
      have h2 : ∑ k ∈ s \ s₀, a k.1 k.2 • (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2) ∈ W M := by
        refine sum_smul_mem (hWbal M) (hWconv M) (hW0 M) _ _ _ (fun k hk => ?_) ?_
        · have hk' : M + 1 ≤ k.1 := by
            by_contra hlt
            rw [Finset.mem_sdiff] at hk
            refine hk.2 ?_
            rw [hs₀, Finset.mem_sigma]
            exact ⟨Finset.mem_range.2 (by omega), Finset.mem_univ _⟩
          exact htmulW M _ (hXU M k.1 hk' k.2).1 _ (hXU M k.1 hk' k.2).2
        · have := sum_sigma_le (fun k : Σ n, ι n => ‖a k.1 k.2‖) (fun k => norm_nonneg _) ε hεsum
            hale (s \ s₀)
          rwa [hεtsum] at this
      have h3 : ∑ k ∈ s \ s₀, a k.1 k.2 • i (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2)
          = i (∑ k ∈ s \ s₀, a k.1 k.2 • (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => (map_smul i _ _).symm
      rw [h3]
      exact hMW ⟨_, h2, rfl⟩
    have hsplit : ∑ k ∈ s, a k.1 k.2 • i (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2)
        = z + (i (u M) - z) + ∑ k ∈ s \ s₀, a k.1 k.2 • i (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2) := by
      rw [← Finset.sum_sdiff hs, hhead]
      abel
    show ∑ k ∈ s, a k.1 k.2 • i (X k.1 k.2 ⊗ₜ[ℂ] Yv k.1 k.2) ∈ N
    rw [hsplit]
    exact hN₁sub (mk_mem_prod (hMP (hu1 M)) htail)

/-- Passage from a countable index type to `ℕ`. -/
theorem reindex {E F : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : E ⊗[ℂ] F →ₗ[ℂ] Y) (z : Y) {κ : Type} [Countable κ]
    (c : κ → ℂ) (x : κ → E) (y : κ → F)
    (hc : Summable (fun k => ‖c k‖)) (hx : Tendsto x cofinite (𝓝 0))
    (hy : Tendsto y cofinite (𝓝 0)) (hsum : HasSum (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) z) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F), Summable (fun k => ‖c k‖) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasSum (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) z := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat κ
  refine ⟨Function.extend g c 0, Function.extend g x 0, Function.extend g y 0, ?_,
    tendsto_extend_zero hg hx, tendsto_extend_zero hg hy, ?_⟩
  · have h : (fun n => ‖Function.extend g c 0 n‖) = Function.extend g (fun k => ‖c k‖) 0 := by
      funext n
      by_cases h : ∃ k, g k = n
      · obtain ⟨k, rfl⟩ := h
        rw [hg.extend_apply, hg.extend_apply]
      · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
        simp
    rw [h]
    exact (summable_extend_zero hg).2 hc
  · have h : (fun n => Function.extend g c 0 n •
        i (Function.extend g x 0 n ⊗ₜ[ℂ] Function.extend g y 0 n))
        = Function.extend g (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) 0 := by
      funext n
      by_cases h : ∃ k, g k = n
      · obtain ⟨k, rfl⟩ := h
        rw [hg.extend_apply, hg.extend_apply, hg.extend_apply, hg.extend_apply]
      · rw [Function.extend_apply' c _ _ h,
          Function.extend_apply' (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) _ _ h]
        simp
    rw [h]
    exact (hasSum_extend_zero hg).2 hsum

end main

end Sol_MasulloGRH_completedProjTensor_exists_series

open MasulloGRH in
theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsFrechet E) (hF : IsFrechet F)
    (Y : Type v) [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : E ⊗[ℂ] F →ₗ[ℂ] Y) (hi : IsCompletedProjTensor E F i) (z : Y) :
    ∃ (c : ℕ → ℂ) (x : ℕ → E) (y : ℕ → F), Summable (fun k => ‖c k‖) ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
      HasSum (fun k => c k • i (x k ⊗ₜ[ℂ] y k)) z := by
  obtain ⟨κ, _, c, x, y, hc, hx, hy, hsum⟩ :=
    Sol_MasulloGRH_completedProjTensor_exists_series.exists_family E F hE hF Y i hi z
  exact Sol_MasulloGRH_completedProjTensor_exists_series.reindex i z c x y hc hx hy hsum
