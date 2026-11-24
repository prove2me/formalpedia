-- Prove2me | solution 1 for GlobalTheory.GaloisPowerRoots.isLocalRing_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:49.197803+00:00
-- url     : https://prove2.me/submissions/60824e1e-9e59-4ac9-bbce-bf5d5519d72d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots
namespace GlobalTheory.GaloisPowerRoots
theorem _root_.solution {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [hH : HenselianLocalRing A] :
    IsLocalRing B := by
  classical
  cases nonempty_fintype G
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal B
  have hunder : ∀ P : Ideal B, P.IsMaximal → P.under A = maximalIdeal A := fun P hP =>
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
  suffices hs : ∀ σ : G, σ • Q = Q by
    refine IsLocalRing.of_unique_max_ideal ⟨Q, hQ, fun P hP => ?_⟩
    haveI := hP.isPrime
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q P
      ((hunder Q hQ).trans (hunder P hP).symm)
    rw [hg, hs]
  have hmax : ∀ σ : G, (σ • Q).IsMaximal := fun σ => by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_equiv _
  have hb : ∀ σ : G, ∃ b : B, b - 1 ∈ Q ∧ (σ • Q ≠ Q → b ∈ σ • Q) := by
    intro σ
    by_cases h : σ • Q = Q
    · exact ⟨1, by simp, fun h' => (h' h).elim⟩
    · have := (hmax σ).coprime_of_ne hQ h
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp this)
      refine ⟨x, ?_, fun _ => hx⟩
      have : x - 1 = -y := by rw [← hxy]; ring
      rw [this]; exact Q.neg_mem hy
  choose b hb1 hb2 using hb
  let φ := Ideal.Quotient.mk Q
  have hφ1 : ∀ x : B, x - 1 ∈ Q ↔ φ x = 1 := fun x => by
    rw [← map_one φ, Ideal.Quotient.eq]
  have hφ0 : ∀ x : B, x ∈ Q ↔ φ x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem.symm
  set β := ∏ σ : G, b σ with hβ
  have hβ1 : β - 1 ∈ Q := by
    rw [hφ1, hβ, map_prod]
    exact Finset.prod_eq_one fun σ _ => (hφ1 _).mp (hb1 σ)
  have hβ2 : ∀ σ : G, σ • Q ≠ Q → σ • β ∈ Q := by
    intro σ hσ
    have h1 : σ⁻¹ • Q ≠ Q := fun h => hσ (by rw [← h, smul_inv_smul, h])
    rw [← Ideal.mem_inv_pointwise_smul_iff]
    exact Ideal.prod_mem _ (Finset.mem_univ σ⁻¹) (hb2 _ h1)
  let H := MulAction.stabilizer G Q
  set γ := ∏ h : H, (h : G) • β with hγ
  have hγ1 : φ γ = 1 := by
    rw [hγ, map_prod]
    refine Finset.prod_eq_one fun h _ => (hφ1 _).mp ?_
    have h2 : (h : G) • Q = Q := h.2
    have := Ideal.smul_mem_pointwise_smul (h : G) _ _ hβ1
    rwa [h2, smul_sub, smul_one] at this
  have hγ2 : ∀ σ : G, σ • Q = Q → σ • γ = γ := fun σ hσ =>
    Finset.smul_prod_perm (G := H) β ⟨σ, hσ⟩
  have hγ3 : ∀ σ : G, σ • Q ≠ Q → φ (σ • γ) = 0 := by
    intro σ hσ
    rw [← hφ0, hγ, Finset.smul_prod']
    refine Ideal.prod_mem _ (Finset.mem_univ (1 : H)) ?_
    simpa using hβ2 σ hσ
  let O : Finset B := Finset.univ.image fun σ : G => σ • γ
  have hγO : γ ∈ O := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, one_smul _ _⟩
  have hO : ∀ δ ∈ O.erase γ, φ δ = 0 := by
    intro δ hδ
    obtain ⟨hne, hδ⟩ := Finset.mem_erase.mp hδ
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hδ
    exact hγ3 σ fun h => hne (hγ2 σ h)
  set f : B[X] := ∏ δ ∈ O, (X - C δ) with hf
  have hfm : f.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hfinv : ∀ σ : G, σ • f = f := by
    intro σ
    rw [hf, Finset.smul_prod']
    simp only [smul_sub, smul_X, smul_C]
    refine Finset.prod_nbij' (fun δ => σ • δ) (fun δ => σ⁻¹ • δ) ?_ ?_ ?_ ?_ ?_
    · intro δ hδ
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hδ
      exact Finset.mem_image.mpr ⟨σ * τ, Finset.mem_univ _, mul_smul _ _ _⟩
    · intro δ hδ
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hδ
      exact Finset.mem_image.mpr ⟨σ⁻¹ * τ, Finset.mem_univ _, mul_smul _ _ _⟩
    · intro δ _; simp
    · intro δ _; simp
    · intro δ _; rfl
  have hlift : f ∈ Polynomial.lifts (algebraMap A B) :=
    f.lifts_iff_coeff_lifts.mpr fun n =>
      Algebra.IsInvariant.isInvariant (G := G) _ fun σ => by rw [← coeff_smul, hfinv]
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hfm
  have hfφ : f.map φ = (X - 1) * X ^ (O.erase γ).card := by
    rw [hf, ← Finset.mul_prod_erase O _ hγO, Polynomial.map_mul, Polynomial.map_prod,
      ← Finset.prod_const]
    congr 1
    · simp [hγ1]
    · refine Finset.prod_congr rfl fun δ hδ => ?_
      simp [hO δ hδ]
  have hmem : ∀ a : A, a ∈ maximalIdeal A ↔ φ (algebraMap A B a) = 0 := fun a => by
    rw [← hunder Q hQ, ← hφ0]; rfl
  have hev : ∀ q : A[X], φ (algebraMap A B (q.eval 1)) = ((q.map (algebraMap A B)).map φ).eval 1 :=
    fun q => by rw [eval_one_map, eval_one_map]
  haveI : Nontrivial (B ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  obtain ⟨a, ha1, ha2⟩ := hH.is_henselian p hp2 1
    (by rw [hmem, hev, hp1, hfφ]; simp)
    (by
      rw [← notMem_maximalIdeal, hmem, hev, ← derivative_map, ← derivative_map, hp1, hfφ]
      simp)
  have ha3 : φ (algebraMap A B a) = 1 := by
    rw [hmem, map_sub, map_sub, map_one, map_one, sub_eq_zero] at ha2
    exact ha2
  have ha4 : f.eval (algebraMap A B a) = 0 := by
    rw [← hp1, eval_map_algebraMap, aeval_algebraMap_apply, coe_aeval_eq_eval, ha1.eq_zero, map_zero]
  rw [hf, eval_prod, Finset.prod_eq_zero_iff] at ha4
  obtain ⟨δ, hδ, hδ2⟩ := ha4
  have hδ3 : algebraMap A B a = δ := by simpa [sub_eq_zero] using hδ2
  have hδ4 : δ = γ := by
    by_contra hne
    have := hO δ (Finset.mem_erase.mpr ⟨hne, hδ⟩)
    rw [← hδ3, ha3] at this
    exact one_ne_zero this
  intro σ
  by_contra hσ
  have := hγ3 σ hσ
  rw [← hδ4, ← hδ3, smul_algebraMap, ha3] at this
  exact one_ne_zero this
end GlobalTheory.GaloisPowerRoots
