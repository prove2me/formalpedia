-- Prove2me | solution 1 for ListHashFurstenberg.Main.lemma_2_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:17:39.339207+00:00
-- url     : https://prove2.me/submissions/7bd4a55f-ef23-48f5-b3be-4463975e9f6f

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg

section
set_option autoImplicit false

namespace ListHashFurstenberg.Main.Dev.GLTool

open Module

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

set_option linter.unusedSectionVars false

instance finite_submodule : Finite (Submodule F (Fin n → F)) :=
  Finite.of_injective (fun U : Submodule F (Fin n → F) => (U : Set (Fin n → F)))
    SetLike.coe_injective

instance finite_linearEquiv : Finite ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
  Finite.of_injective
    (fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => (g : (Fin n → F) → (Fin n → F)))
    (fun _ _ e => LinearEquiv.ext (congrFun e))

noncomputable instance fintype_submodule : Fintype (Submodule F (Fin n → F)) :=
  Fintype.ofFinite _

noncomputable instance fintype_linearEquiv : Fintype ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
  Fintype.ofFinite _

open Classical in
/-- `U` has a translate meeting `S` in at least `T` points. -/
def Rich (T : ℝ) (S : Finset (Fin n → F)) (U : Submodule F (Fin n → F)) : Prop :=
  ∃ x : Fin n → F, T ≤ ((S.filter fun s => s - x ∈ U).card : ℝ)

/-- The `r`-dimensional subspaces of `F^n`. -/
noncomputable def Gr (F : Type*) [Field F] [Fintype F] (n r : ℕ) :
    Finset (Submodule F (Fin n → F)) :=
  Finset.univ.filter (fun U => finrank F U = r)

theorem mem_Gr {r : ℕ} {U : Submodule F (Fin n → F)} : U ∈ Gr F n r ↔ finrank F U = r := by
  simp [Gr]

open Classical in
theorem richFraction_eq (r : ℕ) (T : ℝ) (S : Finset (Fin n → F)) :
    richFraction n r T S =
      (((Gr F n r).filter (Rich T S)).card : ℝ) / ((Gr F n r).card : ℝ) := by
  have e : richFraction n r T S =
      (Nat.card {U : Submodule F (Fin n → F) // finrank F U = r ∧ Rich T S U} : ℝ) /
        (Nat.card {U : Submodule F (Fin n → F) // finrank F U = r} : ℝ) := rfl
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, Gr, Finset.filter_filter]

theorem richFraction_le_one (r : ℕ) (T : ℝ) (S : Finset (Fin n → F)) :
    richFraction n r T S ≤ 1 := by
  classical
  rw [richFraction_eq]
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_filter_le _ _

theorem richFraction_eq_zero (r : ℕ) (T : ℝ) (S : Finset (Fin n → F))
    (h : (Gr F n r).card = 0) : richFraction n r T S = 0 := by
  classical
  rw [richFraction_eq, h, Nat.cast_zero, div_zero]

theorem map_trans (W : Submodule F (Fin n → F)) (g h : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    W.map (g.trans h).toLinearMap = (W.map g.toLinearMap).map h.toLinearMap := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem map_refl (W : Submodule F (Fin n → F)) :
    W.map (LinearEquiv.refl F (Fin n → F)).toLinearMap = W := by
  ext x
  simp

theorem map_map_symm (W : Submodule F (Fin n → F)) (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (W.map g.toLinearMap).map g.symm.toLinearMap = W := by
  rw [← map_trans, LinearEquiv.self_trans_symm, map_refl]

/-- Transitivity of `GL_n` on subspaces of equal dimension. -/
theorem exists_map_eq {W U : Submodule F (Fin n → F)} (h : finrank F W = finrank F U) :
    ∃ g : (Fin n → F) ≃ₗ[F] (Fin n → F), W.map g.toLinearMap = U := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl U
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hD
  have hCD : finrank F C = finrank F D := by omega
  let e1 : W ≃ₗ[F] U := LinearEquiv.ofFinrankEq W U h
  let e2 : C ≃ₗ[F] D := LinearEquiv.ofFinrankEq C D hCD
  let g : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (Submodule.prodEquivOfIsCompl W C hC).symm.trans
      ((e1.prodCongr e2).trans (Submodule.prodEquivOfIsCompl U D hD))
  refine ⟨g, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ W := hw
    have e : (g : (Fin n → F) →ₗ[F] (Fin n → F)) w = (e1 ⟨w, hw'⟩ : Fin n → F) := by
      change (Submodule.prodEquivOfIsCompl U D hD) ((e1.prodCongr e2)
        ((Submodule.prodEquivOfIsCompl W C hC).symm ((⟨w, hw'⟩ : ↥W) : Fin n → F))) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left (h := hC) (x := (⟨w, hw'⟩ : ↥W))]
      simp
    rw [e]
    exact (e1 ⟨w, hw'⟩).2
  · rw [LinearEquiv.finrank_map_eq, h]

theorem card_fiber_eq {r : ℕ} {W U : Submodule F (Fin n → F)} (hW : finrank F W = r)
    (hU : finrank F U = r) :
    (Finset.univ.filter fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => W.map g.toLinearMap = U).card =
      (Finset.univ.filter fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => W.map g.toLinearMap = W).card := by
  obtain ⟨g0, hg0⟩ := exists_map_eq (hW.trans hU.symm)
  refine Finset.card_bij' (fun (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) _ => g.trans g0.symm)
    (fun (g : (Fin n → F) ≃ₗ[F] (Fin n → F)) _ => g.trans g0) ?_ ?_ ?_ ?_
  · intro g hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [map_trans, (Finset.mem_filter.mp hg).2, ← hg0, map_map_symm]
  · intro g hg
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [map_trans, (Finset.mem_filter.mp hg).2, hg0]
  · intro g _
    ext x
    simp
  · intro g _
    ext x
    simp

/-- **Averaging over `GL_n`**: `g ↦ g(W)` hits every `r`-dimensional subspace equally often. -/
theorem sum_map_mul {r : ℕ} {W : Submodule F (Fin n → F)} (hW : finrank F W = r)
    (f : Submodule F (Fin n → F) → ℝ) :
    (∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F), f (W.map g.toLinearMap)) * (Gr F n r).card =
      (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ) * ∑ U ∈ Gr F n r, f U := by
  classical
  set c := (Finset.univ.filter fun g : (Fin n → F) ≃ₗ[F] (Fin n → F) => W.map g.toLinearMap = W).card
    with hc
  have hmaps : ∀ g ∈ (Finset.univ : Finset ((Fin n → F) ≃ₗ[F] (Fin n → F))),
      W.map g.toLinearMap ∈ Gr F n r := by
    intro g _
    rw [mem_Gr, LinearEquiv.finrank_map_eq, hW]
  have hsum : ∀ φ : Submodule F (Fin n → F) → ℝ,
      ∑ g : (Fin n → F) ≃ₗ[F] (Fin n → F), φ (W.map g.toLinearMap) = ∑ U ∈ Gr F n r, (c : ℝ) * φ U := by
    intro φ
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
      Finset.sum_const, nsmul_eq_mul, card_fiber_eq hW (mem_Gr.mp hU)]
  have hcard : (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ) =
      (c : ℝ) * (Gr F n r).card := by
    have := hsum (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [this, mul_comm]
  rw [hsum f, hcard, ← Finset.mul_sum]
  ring

end ListHashFurstenberg.Main.Dev.GLTool
end

section
set_option autoImplicit false

namespace ListHashFurstenberg.Main.Dev.Lemma216

open ListHashFurstenberg.Main.Dev.GLTool Module

/-- Richness is monotone in the set. -/
theorem rich_mono {F : Type*} [Field F] [Fintype F] {n : ℕ} {T : ℝ}
    {S S' : Finset (Fin n → F)} (h : S ⊆ S') {U : Submodule F (Fin n → F)}
    (hU : Rich T S U) : Rich T S' U := by
  classical
  obtain ⟨x, hx⟩ := hU
  refine ⟨x, le_trans hx ?_⟩
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- If `g(U)` is rich for `S` then `U` is rich for `g⁻¹(S)`. -/
theorem rich_image {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} {T : ℝ}
    {S : Finset (Fin n → F)} (g : (Fin n → F) ≃ₗ[F] (Fin n → F))
    {U : Submodule F (Fin n → F)} (hU : Rich T S (U.map g.toLinearMap)) :
    Rich T (S.image g.symm) U := by
  classical
  obtain ⟨x, hx⟩ := hU
  refine ⟨g.symm x, le_trans hx ?_⟩
  have hsub : (S.filter fun s => s - x ∈ U.map g.toLinearMap).image g.symm ⊆
      (S.image g.symm).filter fun s => s - g.symm x ∈ U := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hsS, hsx⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hsS, ?_⟩
    rw [← map_sub]
    obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp hsx
    rw [← hux]
    simpa using hu
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ g.symm.injective] at h2
  exact_mod_cast h2

end ListHashFurstenberg.Main.Dev.Lemma216

namespace ListHashFurstenberg.Main

open ListHashFurstenberg.Main.Dev.Lemma216 ListHashFurstenberg.Main.Dev.GLTool in
theorem chk_lemma_2_16 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (T ε δ : ℝ) (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ < 1)
    (S : Finset (Fin n → F)) (hS : IsFurstenberg ε n r T S) :
    ∃ S' : Finset (Fin n → F), IsFurstenberg δ n r T S' ∧
      (S'.card : ℝ) ≤ (⌈Real.log (1 - δ) / Real.log (1 - ε)⌉ : ℝ) * S.card := by
  classical
  set ρ := richFraction n r T S with hρdef
  have hρε : ε ≤ ρ := hS
  have hρ1 : ρ ≤ 1 := richFraction_le_one r T S
  set D := (Gr F n r).card with hD
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h
    · have := richFraction_eq_zero r T S h0
      linarith
    · exact h
  have hDpos' : (0 : ℝ) < D := by exact_mod_cast hDpos
  -- the number of rotations
  have hlε : Real.log (1 - ε) < 0 := Real.log_neg (by linarith) (by linarith)
  have hlδ : Real.log (1 - δ) < Real.log (1 - ε) := Real.log_lt_log (by linarith) (by linarith)
  set L := Real.log (1 - δ) / Real.log (1 - ε) with hL
  have hLpos : 0 < L := div_pos_of_neg_of_neg (by linarith) hlε
  set K : ℕ := (⌈L⌉).toNat with hK
  have hKL : (K : ℝ) = (⌈L⌉ : ℝ) := by
    have : 0 ≤ ⌈L⌉ := Int.ceil_nonneg hLpos.le
    rw [hK]
    exact_mod_cast Int.toNat_of_nonneg this
  have hLK : L ≤ K := by
    rw [hKL]
    exact Int.le_ceil L
  have hpowε : (1 - ε) ^ K ≤ 1 - δ := by
    have h1 : (K : ℝ) * Real.log (1 - ε) ≤ Real.log (1 - δ) := by
      have := mul_le_mul_of_nonpos_right hLK hlε.le
      rw [hL, div_mul_cancel₀ _ hlε.ne] at this
      linarith
    rw [← Real.log_le_log_iff (pow_pos (by linarith) K) (by linarith), Real.log_pow]
    exact h1
  have hpowρ : (1 - ρ) ^ K ≤ (1 - ε) ^ K := pow_le_pow_left₀ (by linarith) (by linarith) K
  -- the rotated unions
  let S' : (Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F))) → Finset (Fin n → F) :=
    fun t => Finset.univ.biUnion fun i => S.image (t i).symm
  have hcard : ∀ t, (S' t).card ≤ K * S.card := by
    intro t
    calc (S' t).card ≤ ∑ i, (S.image (t i).symm).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin K, S.card := Finset.sum_le_sum fun i _ => Finset.card_image_le
      _ = K * S.card := by simp
  let f : Submodule F (Fin n → F) → ((Fin n → F) ≃ₗ[F] (Fin n → F)) → ℝ :=
    fun U g => if Rich T S (U.map g.toLinearMap) then 1 else 0
  have hfsum : ∀ U ∈ Gr F n r, ∑ g, f U g =
      (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ) * ρ := by
    intro U hU
    have := sum_map_mul (mem_Gr.mp hU) (fun U' => if Rich T S U' then (1 : ℝ) else 0)
    simp only [f, Finset.sum_boole] at this ⊢
    rw [hρdef, richFraction_eq, mul_div_assoc', eq_div_iff hDpos'.ne']
    exact this
  have hpt : ∀ (t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F))) (U : Submodule F (Fin n → F)),
      1 - ∏ i, (1 - f U (t i)) ≤ (if Rich T (S' t) U then (1 : ℝ) else 0) := by
    intro t U
    by_cases h : ∃ i, Rich T S (U.map (t i).toLinearMap)
    · obtain ⟨i, hi⟩ := h
      have hR : Rich T (S' t) U :=
        rich_mono (Finset.subset_biUnion_of_mem _ (Finset.mem_univ i)) (rich_image (t i) hi)
      rw [if_pos hR]
      have : 0 ≤ ∏ j, (1 - f U (t j)) := Finset.prod_nonneg fun j _ => by
        simp only [f]
        split_ifs <;> norm_num
      linarith
    · push Not at h
      have : ∏ i, (1 - f U (t i)) = 1 := Finset.prod_eq_one fun i _ => by simp [f, h i]
      rw [this]
      split_ifs <;> norm_num
  set c : ℝ := (Fintype.card ((Fin n → F) ≃ₗ[F] (Fin n → F)) : ℝ) with hc
  have hsum : ∑ _t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)), (D : ℝ) * (1 - (1 - ρ) ^ K) ≤
      ∑ t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)),
        (((Gr F n r).filter (Rich T (S' t))).card : ℝ) := by
    calc ∑ _t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)), (D : ℝ) * (1 - (1 - ρ) ^ K)
        = ∑ U ∈ Gr F n r, ∑ t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)),
            (1 - ∏ i, (1 - f U (t i))) := by
          have hU : ∀ U ∈ Gr F n r, ∑ t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)),
              (1 - ∏ i, (1 - f U (t i))) = c ^ K * (1 - (1 - ρ) ^ K) := by
            intro U hU
            have e1 : ∑ t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)), ∏ i, (1 - f U (t i)) =
                (∑ g, (1 - f U g)) ^ K := by
              rw [Fintype.sum_pow]
            have e2 : ∑ g, (1 - f U g) = c * (1 - ρ) := by
              rw [Finset.sum_sub_distrib, hfsum U hU]
              simp [hc]
              ring
            rw [Finset.sum_sub_distrib, e1, e2, mul_pow]
            simp [hc]
            ring
          rw [Finset.sum_congr rfl hU, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
            nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
      _ ≤ ∑ U ∈ Gr F n r, ∑ t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)),
            (if Rich T (S' t) U then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun U _ => Finset.sum_le_sum fun t _ => hpt t U
      _ = ∑ t : Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)),
            ∑ U ∈ Gr F n r, (if Rich T (S' t) U then (1 : ℝ) else 0) := Finset.sum_comm
      _ = _ := by simp only [Finset.sum_boole]
  have hne : (Finset.univ : Finset (Fin K → ((Fin n → F) ≃ₗ[F] (Fin n → F)))).Nonempty :=
    ⟨fun _ => LinearEquiv.refl F _, Finset.mem_univ _⟩
  obtain ⟨t, -, ht⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨S' t, ?_, ?_⟩
  · show δ ≤ richFraction n r T (S' t)
    rw [richFraction_eq, le_div_iff₀ hDpos']
    have : δ ≤ 1 - (1 - ρ) ^ K := by linarith
    have := mul_le_mul_of_nonneg_left this hDpos'.le
    linarith
  · have h1 : ((S' t).card : ℝ) ≤ (K : ℝ) * S.card := by exact_mod_cast hcard t
    rw [hKL] at h1
    exact h1

end ListHashFurstenberg.Main
end

theorem solution : type_of% @ListHashFurstenberg.Main.chk_lemma_2_16 := @ListHashFurstenberg.Main.chk_lemma_2_16
