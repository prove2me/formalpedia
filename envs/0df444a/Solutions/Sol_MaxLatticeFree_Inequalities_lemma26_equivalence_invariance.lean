-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.lemma26_equivalence_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:36:54.145359+00:00
-- url     : https://prove2.me/submissions/ccf90a5c-ac6f-48b5-82a8-22a6cf42fad2

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

set_option autoImplicit false

namespace MaxLatticeFree.Inequalities.L26aux

open MaxLatticeFree.Inequalities Matrix

variable {q : ℕ}

noncomputable def gmap {ℓ : ℕ} (C : Matrix (Fin ℓ) (Fin q) ℝ) (lam : Fin ℓ → ℝ) :
    EuclideanSpace ℝ (Fin q) →ₗ[ℝ] ℝ where
  toFun x := lam ⬝ᵥ (C *ᵥ x.ofLp)
  map_add' x y := by simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [Matrix.mulVec_smul, dotProduct_smul]

lemma linVal_affine {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (φ : W → ℝ)
    (g : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] ℝ) (ρ : ℝ) (s : W →₀ ℝ) :
    linVal (fun r => ρ * φ r + g (r : EuclideanSpace ℝ (Fin q))) s
      = ρ * linVal φ s + g (combo W s) := by
  unfold linVal combo Finsupp.sum
  rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

lemma combo_mem (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (s : W →₀ ℝ) :
    combo W s ∈ W := by
  unfold combo Finsupp.sum
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ r.2

lemma gmap_on_Rf {ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (C : Matrix (Fin ℓ) (Fin q) ℝ)
    (d : Fin ℓ → ℝ) (lam : Fin ℓ → ℝ) (hdesc : IsAffineHullDescription f W C d)
    (s : W →₀ ℝ) (hs : s ∈ Rf f W) :
    gmap C lam (combo W s) = lam ⬝ᵥ (d - C *ᵥ f.ofLp) := by
  have hx : f + combo W s ∈ (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) := by
    apply subset_affineSpan
    refine ⟨?_, hs.1⟩
    show f + combo W s - f ∈ W
    simpa using combo_mem W s
  have h2 : f + combo W s ∈ {x : EuclideanSpace ℝ (Fin q) | x ∈ affSpace f W ∧ C *ᵥ x.ofLp = d} :=
    hdesc ▸ hx
  have h3 : C *ᵥ (f + combo W s).ofLp = d := h2.2
  rw [WithLp.ofLp_add, Matrix.mulVec_add] at h3
  have h4 : C *ᵥ (combo W s).ofLp = d - C *ᵥ f.ofLp := by rw [← h3]; abel
  show lam ⬝ᵥ (C *ᵥ (combo W s).ofLp) = _
  rw [h4]

section transfer

variable (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
  (g : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] ℝ) (ρ κ : ℝ)

/-- the affine transform `φ ↦ ρ φ + g` -/
noncomputable def T (φ : W → ℝ) : W → ℝ := fun r => ρ * φ r + g (r : EuclideanSpace ℝ (Fin q))

noncomputable def Tinv (φ : W → ℝ) : W → ℝ := fun r => (φ r - g (r : EuclideanSpace ℝ (Fin q))) / ρ

lemma T_Tinv (hρ : 0 < ρ) (φ : W → ℝ) : T W g ρ (Tinv W g ρ φ) = φ := by
  funext r
  unfold T Tinv
  field_simp
  ring

lemma T_inj (hρ : 0 < ρ) {φ₁ φ₂ : W → ℝ} (h : T W g ρ φ₁ = T W g ρ φ₂) : φ₁ = φ₂ := by
  funext r
  have := congrFun h r
  unfold T at this
  exact mul_left_cancel₀ hρ.ne' (by linarith)

lemma dom_T_iff (hρ : 0 < ρ) (φ₁ φ₂ : W → ℝ) :
    Dominates (T W g ρ φ₁) (T W g ρ φ₂) ↔ Dominates φ₁ φ₂ := by
  unfold Dominates T
  constructor
  · intro h r
    have := h r
    exact le_of_mul_le_mul_left (by linarith) hρ
  · intro h r
    have := mul_le_mul_of_nonneg_left (h r) hρ.le
    linarith

lemma valid_T_iff (hρ : 0 < ρ) (hg : ∀ s ∈ Rf f W, g (combo W s) = κ) (φ : W → ℝ) (α' : ℝ) :
    IsValid f W (T W g ρ φ) (ρ * α' + κ) ↔ IsValid f W φ α' := by
  unfold IsValid
  constructor
  · intro h s hs
    have h1 := h s hs
    unfold T at h1
    rw [linVal_affine, hg s hs] at h1
    exact le_of_mul_le_mul_left (by linarith) hρ
  · intro h s hs
    unfold T
    rw [linVal_affine, hg s hs]
    have := mul_le_mul_of_nonneg_left (h s hs) hρ.le
    linarith

lemma minimal_T_iff (hρ : 0 < ρ) (hg : ∀ s ∈ Rf f W, g (combo W s) = κ) (φ : W → ℝ) (α' : ℝ) :
    IsMinimal f W (T W g ρ φ) (ρ * α' + κ) ↔ IsMinimal f W φ α' := by
  unfold IsMinimal
  rw [valid_T_iff f W g ρ κ hρ hg]
  constructor
  · rintro ⟨hv, hmin⟩
    refine ⟨hv, fun χ hχ hdom => ?_⟩
    apply T_inj W g ρ hρ
    apply hmin
    · exact (valid_T_iff f W g ρ κ hρ hg χ α').2 hχ
    · exact (dom_T_iff W g ρ hρ χ φ).2 hdom
  · rintro ⟨hv, hmin⟩
    refine ⟨hv, fun χ hχ hdom => ?_⟩
    rw [← T_Tinv W g ρ hρ χ] at hχ hdom ⊢
    congr 1
    apply hmin
    · exact (valid_T_iff f W g ρ κ hρ hg _ α').1 hχ
    · exact (dom_T_iff W g ρ hρ _ φ).1 hdom

lemma sublinear_T_iff (hρ : 0 < ρ) (φ : W → ℝ) :
    IsSublinear (T W g ρ φ) ↔ IsSublinear φ := by
  unfold IsSublinear IsPositivelyHomogeneous IsSubadditive T
  simp only [Submodule.coe_smul, Submodule.coe_add, map_smul, map_add, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r c hc => ?_, fun r₁ r₂ => ?_⟩
    · have := h1 r c hc
      exact mul_left_cancel₀ hρ.ne' (by linear_combination this)
    · have := h2 r₁ r₂
      exact le_of_mul_le_mul_left (by linarith) hρ
  · rintro ⟨h1, h2⟩
    refine ⟨fun r c hc => ?_, fun r₁ r₂ => ?_⟩
    · rw [h1 r c hc]; ring
    · have := mul_le_mul_of_nonneg_left (h2 r₁ r₂) hρ.le
      linarith

end transfer

end MaxLatticeFree.Inequalities.L26aux

open MaxLatticeFree.Inequalities Matrix in
theorem solution {q ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (ψ ψ' : W → ℝ) (α α' : ℝ)
    (hequiv : Equivalent f W C d ψ α ψ' α') :
    (IsSublinear ψ ↔ IsSublinear ψ') ∧
    ((∃ φ : W → ℝ, IsMinimal f W φ α ∧ Dominates φ ψ) ↔
        (∃ φ' : W → ℝ, IsMinimal f W φ' α' ∧ Dominates φ' ψ')) ∧
    (IsMinimal f W ψ α ↔ IsMinimal f W ψ' α') := by
  obtain ⟨hdesc, -, -, ρ, hρ, lam, hψ, hα⟩ := hequiv
  have hg : ∀ s ∈ Rf f W, L26aux.gmap C lam (combo W s) = lam ⬝ᵥ (d - C *ᵥ f.ofLp) :=
    fun s hs => L26aux.gmap_on_Rf f W C d lam hdesc s hs
  have hψeq : ψ = L26aux.T W (L26aux.gmap C lam) ρ ψ' := funext fun r => hψ r
  subst hψeq
  subst hα
  refine ⟨L26aux.sublinear_T_iff W (L26aux.gmap C lam) ρ hρ ψ', ?_,
    L26aux.minimal_T_iff f W (L26aux.gmap C lam) ρ _ hρ hg ψ' α'⟩
  constructor
  · rintro ⟨φ, hmin, hdom⟩
    refine ⟨L26aux.Tinv W (L26aux.gmap C lam) ρ φ, ?_, ?_⟩
    · rw [← L26aux.T_Tinv W (L26aux.gmap C lam) ρ hρ φ] at hmin
      exact (L26aux.minimal_T_iff f W (L26aux.gmap C lam) ρ _ hρ hg _ α').1 hmin
    · rw [← L26aux.T_Tinv W (L26aux.gmap C lam) ρ hρ φ] at hdom
      exact (L26aux.dom_T_iff W (L26aux.gmap C lam) ρ hρ _ ψ').1 hdom
  · rintro ⟨φ', hmin, hdom⟩
    exact ⟨L26aux.T W (L26aux.gmap C lam) ρ φ', (L26aux.minimal_T_iff f W (L26aux.gmap C lam) ρ _ hρ hg φ' α').2 hmin,
      (L26aux.dom_T_iff W (L26aux.gmap C lam) ρ hρ φ' ψ').2 hdom⟩
