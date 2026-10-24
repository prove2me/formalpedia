-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_8
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:39:57.402645+00:00
-- url     : https://prove2.me/submissions/c5145793-08ae-4701-8942-2a603b5c1575

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic.SandwichProof

lemma sandwich_of_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Set E) (hI : Convex ℝ I)
    (hInt : (interior I).Nonempty) (f g : E → ℝ)
    (hf : ConvexOn ℝ I f) (hg : ConcaveOn ℝ I g) (hgf : ∀ z ∈ I, g z ≤ f z) :
    ∃ (l : E →ₗ[ℝ] ℝ) (K : ℝ), ∀ z ∈ I, g z ≤ l z + K ∧ l z + K ≤ f z := by
  let A : Set (E × ℝ) := {p | p.1 ∈ I ∧ p.2 < g p.1}
  let B : Set (E × ℝ) := {p | p.1 ∈ I ∧ f p.1 ≤ p.2}
  let S : Set (E × ℝ) := {p | p.1 ∈ interior I ∧ p.2 < g p.1}
  have hA : Convex ℝ A := hg.convex_strict_hypograph
  have hB : Convex ℝ B := hf.convex_epigraph
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hgcont : ContinuousAt (fun q : E × ℝ => g q.1) p :=
      ((hg.continuousOn_interior p.1 hp.1).continuousAt
        (isOpen_interior.mem_nhds hp.1)).comp continuous_fst.continuousAt
    exact Filter.inter_mem
      (continuous_fst.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hp.1))
      (continuous_snd.continuousAt.eventually_lt hgcont hp.2)
  have hSint : S ⊆ interior A :=
    interior_maximal (fun p hp => ⟨interior_subset hp.1, hp.2⟩) hSopen
  obtain ⟨x₀, hx₀⟩ := hInt
  have hp₀ : (x₀, g x₀ - 1) ∈ interior A := hSint ⟨hx₀, by linarith⟩
  have hIntA : (interior A).Nonempty := ⟨_, hp₀⟩
  have hdisj : Disjoint (interior A) B := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have hp' : p ∈ A := interior_subset hp
    have hfg := hgf p.1 hp'.1
    exact (hp'.2.trans_le hfg).not_ge hq.2
  obtain ⟨L, u, hLA, hLB⟩ :=
    geometric_hahn_banach_open hA.interior isOpen_interior hB hdisj
  have hLAall (p : E × ℝ) (hp : p ∈ A) : L p ≤ u := by
    have hclosed : closure (interior A) ⊆ {q | L q ≤ u} :=
      closure_minimal (fun q hq => (hLA q hq).le) (isClosed_le L.continuous continuous_const)
    apply hclosed
    rw [hA.closure_interior_eq_closure_of_nonempty_interior hIntA]
    exact subset_closure hp
  have hL (x : E) (r : ℝ) : L (x, r) = L (x, 0) + r * L (0, 1) := by
    have he : (x, r) = (x, 0) + r • (0, 1) := by ext <;> simp
    rw [he, L.map_add, L.map_smul]
    rfl
  have hc : 0 < L (0, 1) := by
    have hlow := hLA (x₀, g x₀ - 1) hp₀
    have hhigh := hLB (x₀, f x₀) ⟨interior_subset hx₀, le_rfl⟩
    rw [hL] at hlow hhigh
    have hgap := hgf x₀ (interior_subset hx₀)
    by_contra hnonpos
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ f x₀ - (g x₀ - 1) by linarith) (le_of_not_gt hnonpos)
    nlinarith
  let l : E →ₗ[ℝ] ℝ := -(L (0, 1))⁻¹ • (L.toLinearMap.comp (LinearMap.inl ℝ E ℝ))
  have hl (x : E) : l x + u / L (0, 1) = (u - L (x, 0)) / L (0, 1) := by
    simp only [l, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.inl_apply,
      ContinuousLinearMap.coe_coe, smul_eq_mul]
    ring
  refine ⟨l, u / L (0, 1), ?_⟩
  intro z hz
  rw [hl]
  constructor
  · by_contra hbad
    let r := ((u - L (z, 0)) / L (0, 1) + g z) / 2
    have hr : r < g z := by dsimp [r]; linarith
    have hsep := hLAall (z, r) ⟨hz, hr⟩
    rw [hL] at hsep
    have hrle : r ≤ (u - L (z, 0)) / L (0, 1) :=
      (le_div_iff₀ hc).mpr (by linarith)
    dsimp [r] at hrle
    linarith
  · apply (div_le_iff₀ hc).mpr
    have hsep := hLB (z, f z) ⟨hz, le_rfl⟩
    rw [hL] at hsep
    linarith

end MICPRep.Periodic.SandwichProof

namespace MICPRep.Periodic.SandwichProof

lemma sandwich_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Set E) (hI : Convex ℝ I) (f g : E → ℝ)
    (hf : ConvexOn ℝ I f) (hg : ConcaveOn ℝ I g) (hgf : ∀ z ∈ I, g z ≤ f z) :
    ∃ (l : E →ₗ[ℝ] ℝ) (K : ℝ), ∀ z ∈ I, g z ≤ l z + K ∧ l z + K ≤ f z := by
  classical
  by_cases hne : I.Nonempty
  · haveI : Nonempty I := hne.to_subtype
    obtain ⟨x₀, hx₀⟩ := hne
    let A := affineSpan ℝ I
    let p₀ : A := ⟨x₀, subset_affineSpan ℝ I hx₀⟩
    let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ p₀
    let φ : A.direction →ᵃ[ℝ] E := A.subtype.comp e.toAffineEquiv.toAffineMap
    let J : Set A.direction := φ ⁻¹' I
    have hJ : Convex ℝ J := hI.affine_preimage φ
    have hspan : affineSpan ℝ J = ⊤ := by
      change affineSpan ℝ (e.toAffineEquiv ⁻¹' (((↑) : A → E) ⁻¹' I)) = ⊤
      rw [← AffineSubspace.comap_span, affineSpan_coe_preimage_eq_top,
        AffineSubspace.comap_top]
    have hInt : (interior J).Nonempty := hJ.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
    obtain ⟨l, K, hl⟩ := sandwich_of_interior J hJ hInt (f ∘ φ) (g ∘ φ)
      (hf.comp_affineMap φ) (hg.comp_affineMap φ) (fun z hz => hgf (φ z) hz)
    obtain ⟨L, hL⟩ := l.exists_extend
    have hLval (w : A.direction) : L (w : E) = l w :=
      congrArg (fun F : A.direction →ₗ[ℝ] ℝ => F w) hL
    have hφ (w : A.direction) : φ w = (w : E) + x₀ := rfl
    refine ⟨L, K - L x₀, ?_⟩
    intro z hz
    let p : A := ⟨z, subset_affineSpan ℝ I hz⟩
    let w : A.direction := e.symm p
    have hw : φ w = z := by
      change ((e (e.symm p) : A) : E) = z
      rw [e.apply_symm_apply]
    have hineq := hl w (show w ∈ J from by change φ w ∈ I; rwa [hw])
    have heq : l w + K = L z + (K - L x₀) := by
      rw [← hw, hφ, L.map_add, hLval]
      ring
    change g (φ w) ≤ l w + K ∧ l w + K ≤ f (φ w) at hineq
    rwa [hw, heq] at hineq
  · refine ⟨0, 0, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

end MICPRep.Periodic.SandwichProof

open MICPRep.Periodic
open scoped ENNReal Matrix

theorem solution {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (f g : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ I f) (hg : ConcaveOn ℝ I g)
    (hgf : ∀ z ∈ I, g z ≤ f z) :
    ∃ (v : Fin d → ℝ) (K : ℝ), ∀ z ∈ I, g z ≤ v ⬝ᵥ z + K ∧ v ⬝ᵥ z + K ≤ f z := by
  classical
  obtain ⟨L, K, hL⟩ := SandwichProof.sandwich_linear I hI f g hf hg hgf
  let v : Fin d → ℝ := fun i => L (fun j => if i = j then 1 else 0)
  have hv (z : Fin d → ℝ) : L z = v ⬝ᵥ z := by
    rw [L.pi_apply_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  refine ⟨v, K, ?_⟩
  intro z hz
  rw [← hv z]
  exact hL z hz
