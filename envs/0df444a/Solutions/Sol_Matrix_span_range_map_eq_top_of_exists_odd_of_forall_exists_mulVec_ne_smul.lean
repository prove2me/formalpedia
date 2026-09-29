-- Prove2me | solution 1 for Matrix.span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c713d923-2f0c-5b8d-b008-3d66ac9c2601

import Mathlib
import Theorems.Thm_Matrix_span_image_map_eq_top_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul

set_option autoImplicit false

namespace BridgeSpanOdd

open Matrix

variable {F : Type*} [Field F]

local notation "M₂" => Matrix (Fin 2) (Fin 2) F

theorem exists_smul_of_mul_eq_zero (e f : M₂) (hef : e * f = 0) {w' : Fin 2 → F} (hf : f *ᵥ w' ≠ 0)
    {w : Fin 2 → F} (hv : e *ᵥ w ≠ 0) (u : Fin 2 → F) :
    ∃ a : F, e *ᵥ u = a • (e *ᵥ w) := by

  have hker : 0 < Module.finrank F (LinearMap.ker e.mulVecLin) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨f *ᵥ w', ?_⟩, fun h => hf (congrArg Subtype.val h)⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hef, Matrix.zero_mulVec]
  have hsum := LinearMap.finrank_range_add_finrank_ker e.mulVecLin
  rw [Module.finrank_fin_fun] at hsum
  have hrange : Module.finrank F (LinearMap.range e.mulVecLin) ≤ 1 := by omega
  obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hrange
  have hmem : ∀ x : Fin 2 → F, e *ᵥ x ∈ LinearMap.range e.mulVecLin := fun x => ⟨x, rfl⟩
  obtain ⟨c₀, hc₀⟩ := hv₀ ⟨e *ᵥ w, hmem w⟩
  obtain ⟨c₁, hc₁⟩ := hv₀ ⟨e *ᵥ u, hmem u⟩
  have hc₀' : c₀ • (v₀ : Fin 2 → F) = e *ᵥ w := congrArg Subtype.val hc₀
  have hc₁' : c₁ • (v₀ : Fin 2 → F) = e *ᵥ u := congrArg Subtype.val hc₁
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₀'
    exact hv hc₀'.symm
  refine ⟨c₁ * c₀⁻¹, ?_⟩
  rw [← hc₁', ← hc₀', smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one]

theorem span_range_eq_top {G : Type*} [Group G] (h2 : (2 : F) ≠ 0)
    (ρ : G →* M₂)
    (hodd : ∃ c : G, ρ c * ρ c = 1 ∧ (ρ c).det = -1)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : G, ∀ c : F, (ρ σ) *ᵥ v ≠ c • v) :
    Submodule.span F (Set.range ρ) = ⊤ := by
  classical
  set A : Submodule F M₂ := Submodule.span F (Set.range ρ) with hA

  have hone : (1 : M₂) ∈ A := Submodule.subset_span ⟨1, map_one ρ⟩
  have hmul : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A := by
    intro X hX Y hY
    have hAA : A * A ≤ A := by
      rw [hA, Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, ⟨g, rfl⟩, y, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, map_mul ρ g h⟩
    exact hAA (Submodule.mul_mem_mul hX hY)
  have hρA : ∀ g, ρ g ∈ A := fun g => Submodule.subset_span ⟨g, rfl⟩

  obtain ⟨c, hc2, hcdet⟩ := hodd
  set C := ρ c with hC
  have hCA : C ∈ A := hρA c
  set ep : M₂ := (2 : F)⁻¹ • (1 + C) with hep
  set em : M₂ := (2 : F)⁻¹ • (1 - C) with hem
  have hepA : ep ∈ A := A.smul_mem _ (A.add_mem hone hCA)
  have hemA : em ∈ A := A.smul_mem _ (A.sub_mem hone hCA)
  have hsum : ep + em = 1 := by
    rw [hep, hem, ← smul_add, add_add_sub_cancel, ← two_smul F (1 : M₂), smul_smul, inv_mul_cancel₀ h2, one_smul]
  have h1C : (1 + C) * (1 - C) = 0 := by
    rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hc2]; abel
  have h1C' : (1 - C) * (1 + C) = 0 := by
    rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hc2]; abel
  have hepem : ep * em = 0 := by
    rw [hep, hem, smul_mul_assoc, mul_smul_comm, h1C, smul_zero, smul_zero]
  have hemep : em * ep = 0 := by
    rw [hep, hem, smul_mul_assoc, mul_smul_comm, h1C', smul_zero, smul_zero]
  have hepep : ep * ep = ep := by
    calc ep * ep = ep * ep + ep * em := by rw [hepem, add_zero]
      _ = ep * (ep + em) := (mul_add _ _ _).symm
      _ = ep := by rw [hsum, mul_one]
  have hemem : em * em = em := by
    calc em * em = em * ep + em * em := by rw [hemep, zero_add]
      _ = em * (ep + em) := (mul_add _ _ _).symm
      _ = em := by rw [hsum, mul_one]

  have hneg1 : (-1 : F) ≠ 1 := by
    intro h; apply h2
    have : (1 : F) + 1 = 0 := by
      calc (1 : F) + 1 = 1 + (-1) := by rw [h]
        _ = 0 := add_neg_cancel 1
    rw [← this]; norm_num
  have hep0 : ep ≠ 0 := by
    intro h
    have h' : (1 : M₂) + C = 0 := by
      rw [hep, smul_eq_zero] at h
      exact h.resolve_left (inv_ne_zero h2)
    have hC' : C = -1 := eq_neg_of_add_eq_zero_right h'
    have : C.det = 1 := by rw [hC', Matrix.det_neg, Matrix.det_one]; norm_num
    exact hneg1 (hcdet.symm.trans this)
  have hem0 : em ≠ 0 := by
    intro h
    have h' : (1 : M₂) - C = 0 := by
      rw [hem, smul_eq_zero] at h
      exact h.resolve_left (inv_ne_zero h2)
    have hC' : C = 1 := (sub_eq_zero.mp h').symm
    have : C.det = 1 := by rw [hC', Matrix.det_one]
    exact hneg1 (hcdet.symm.trans this)

  have hexp : ∃ w, ep *ᵥ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hep0 (Matrix.toLin'.injective (LinearMap.ext fun w => by simpa [Matrix.toLin'_apply] using h w))
  have hexm : ∃ w, em *ᵥ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hem0 (Matrix.toLin'.injective (LinearMap.ext fun w => by simpa [Matrix.toLin'_apply] using h w))
  obtain ⟨wp, hwp⟩ := hexp
  obtain ⟨wm, hwm⟩ := hexm

  have hrkp : ∀ u, ∃ a : F, ep *ᵥ u = a • (ep *ᵥ wp) :=
    exists_smul_of_mul_eq_zero ep em hepem hwm hwp
  have hrkm : ∀ u, ∃ a : F, em *ᵥ u = a • (em *ᵥ wm) :=
    exists_smul_of_mul_eq_zero em ep hemep hwp hwm

  obtain ⟨σ, hσ⟩ := hirr (ep *ᵥ wp) hwp
  obtain ⟨τ, hτ⟩ := hirr (em *ᵥ wm) hwm
  set X := ρ σ with hX
  set Y := ρ τ with hY
  set Nmp : M₂ := em * X * ep with hNmp
  set Npm : M₂ := ep * Y * em with hNpm
  have hNmpA : Nmp ∈ A := hmul _ (hmul _ hemA _ (hρA σ)) _ hepA
  have hNpmA : Npm ∈ A := hmul _ (hmul _ hepA _ (hρA τ)) _ hemA
  have hNmp0 : Nmp ≠ 0 := by
    intro h0

    have h1 : em *ᵥ (X *ᵥ (ep *ᵥ wp)) = 0 := by
      have : Nmp *ᵥ wp = 0 := by rw [h0, Matrix.zero_mulVec]
      rwa [hNmp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this
    obtain ⟨a, ha⟩ := hrkp (X *ᵥ (ep *ᵥ wp))
    have h3 : X *ᵥ (ep *ᵥ wp) = ep *ᵥ (X *ᵥ (ep *ᵥ wp)) + em *ᵥ (X *ᵥ (ep *ᵥ wp)) := by
      rw [← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    rw [h1, add_zero, ha] at h3
    exact hσ a h3
  have hNpm0 : Npm ≠ 0 := by
    intro h0
    have h1 : ep *ᵥ (Y *ᵥ (em *ᵥ wm)) = 0 := by
      have : Npm *ᵥ wm = 0 := by rw [h0, Matrix.zero_mulVec]
      rwa [hNpm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this
    obtain ⟨a, ha⟩ := hrkm (Y *ᵥ (em *ᵥ wm))
    have h3 : Y *ᵥ (em *ᵥ wm) = ep *ᵥ (Y *ᵥ (em *ᵥ wm)) + em *ᵥ (Y *ᵥ (em *ᵥ wm)) := by
      rw [← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    rw [h1, zero_add, ha] at h3
    exact hτ a h3

  have s1 : ∀ Z : M₂, ep * (ep * Z) = ep * Z := fun Z => by rw [← mul_assoc, hepep]
  have s2 : ∀ Z : M₂, ep * (em * Z) = 0 := fun Z => by rw [← mul_assoc, hepem, zero_mul]
  have s3 : ∀ Z : M₂, em * (ep * Z) = 0 := fun Z => by rw [← mul_assoc, hemep, zero_mul]
  have s4 : ∀ Z : M₂, em * (em * Z) = em * Z := fun Z => by rw [← mul_assoc, hemem]

  let b : Fin 4 → M₂ := ![ep, em, Nmp, Npm]
  have hb : ∀ i, b i ∈ A := by
    intro i; fin_cases i
    · exact hepA
    · exact hemA
    · exact hNmpA
    · exact hNpmA
  have hli : LinearIndependent F b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [b, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hg

    have k0 := congrArg (fun Z => ep * Z * ep) hg
    have k1 := congrArg (fun Z => em * Z * em) hg
    have k2 := congrArg (fun Z => em * Z * ep) hg
    have k3 := congrArg (fun Z => ep * Z * em) hg
    simp only [hNmp, hNpm, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, s1, s2, s3, s4,
      hepep, hemem, hepem, hemep, mul_zero, zero_mul, smul_zero, add_zero, zero_add] at k0 k1 k2 k3
    have g0 : g 0 = 0 := by simpa [hep0] using k0
    have g1 : g 1 = 0 := by simpa [hem0] using k1
    have g2 : g 2 = 0 := by
      have : g 2 • Nmp = 0 := by simpa [hNmp, mul_assoc] using k2
      exact (smul_eq_zero.mp this).resolve_right hNmp0
    have g3 : g 3 = 0 := by
      have : g 3 • Npm = 0 := by simpa [hNpm, mul_assoc] using k3
      exact (smul_eq_zero.mp this).resolve_right hNpm0
    intro i; fin_cases i <;> assumption
  have hspan4 : Submodule.span F (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])

  refine eq_top_iff.mpr ?_
  rw [← hspan4, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hb i

end BridgeSpanOdd

theorem solution
    {G : Type*} [Group G] {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) F)
    (hodd : ∃ c : G, ρ c * ρ c = 1 ∧ (ρ c).det = -1)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : G, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    {k : Type*} [Field k] (ι : F →+* k) :
    Submodule.span k (Set.range fun g : G => (ρ g).map ι) = ⊤ := by
  classical
  have hF := BridgeSpanOdd.span_range_eq_top h2 ρ hodd hirr
  have himg : (Set.range fun g : G => (ρ g).map ι) =
      (fun X : Matrix (Fin 2) (Fin 2) F => X.map ι) '' Set.range ρ := by
    ext Z; simp
  rw [himg]
  exact Matrix.span_image_map_eq_top_of_span_eq_top ι hF

end S_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
end P2MW
export P2MW.S_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul (solution)
