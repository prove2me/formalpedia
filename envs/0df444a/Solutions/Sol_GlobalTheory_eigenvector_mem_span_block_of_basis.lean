-- Prove2me | solution 1 for GlobalTheory.eigenvector_mem_span_block_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:32.49459+00:00
-- url     : https://prove2.me/submissions/54305b48-4a9f-4e7b-85ab-b95881b04567

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorMemSpanBlockOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K C : Type) [Field K] [Field C] (ι : K →+* C) (O A : Type) [Fintype A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → K), Function.Injective em → (∀ x q, (M x).mulVec (fun s => ι (u q s)) = em q.1 x • fun s => ι (u q s)) → (∀ z : Fin d → K, ∃! b : (Σ a : A, Fin (n a)) → K, ∀ s, ∑ q, b q * u q s = z s) → ∀ (a : A) (z : Fin d → C), (∀ x, (M x).mulVec z = em a x • z) → ∃ b : Fin (n a) → C, z = ∑ i, b i • fun s => ι (u ⟨a, i⟩ s) := by
  intro K C _ _ ι O A _ n d M em u hem hM hb a z hz
  classical
  let U : Matrix (Σ a : A, Fin (n a)) (Fin d) K := Matrix.of u
  let W : Matrix (Fin d) (Σ a : A, Fin (n a)) K :=
    Matrix.of fun t => (hb (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hb (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := by
    have h1 : U * W * U = U := by rw [Matrix.mul_assoc, hWU, Matrix.mul_one]
    have h2 : (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) * U = U := Matrix.one_mul _
    ext q q'
    have := (hb (u q)).unique (y₁ := (U * W) q)
      (y₂ := (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) q)
      (fun s => by
        have := congrFun (congrFun h1 q) s
        rw [Matrix.mul_apply] at this
        exact this)
      (fun s => by
        have := congrFun (congrFun h2 q) s
        rw [Matrix.mul_apply] at this
        exact this)
    exact congrFun this q'
  have hWU' : W.map ι * U.map ι = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hUW' : U.map ι * W.map ι = 1 := by
    rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hvm : ∀ c : (Σ a : A, Fin (n a)) → C,
      Matrix.vecMul c (U.map ι) = ∑ q, c q • fun s => ι (u q s) := by
    intro c
    funext s
    simp [Matrix.vecMul, dotProduct, U, Finset.sum_apply]
  have hind : ∀ c : (Σ a : A, Fin (n a)) → C,
      (∑ q, c q • fun s => ι (u q s)) = 0 → c = 0 := by
    intro c hc
    rw [← hvm] at hc
    have : Matrix.vecMul (Matrix.vecMul c (U.map ι)) (W.map ι) = c := by
      rw [Matrix.vecMul_vecMul, hUW', Matrix.vecMul_one]
    rw [← this, hc, Matrix.zero_vecMul]
  obtain ⟨c, hc⟩ : ∃ c : (Σ a : A, Fin (n a)) → C, z = ∑ q, c q • fun s => ι (u q s) := by
    refine ⟨Matrix.vecMul z (W.map ι), ?_⟩
    rw [← hvm, Matrix.vecMul_vecMul, hWU', Matrix.vecMul_one]
  have hzero : ∀ q : (Σ a : A, Fin (n a)), q.1 ≠ a → c q = 0 := by
    intro q hq
    by_contra hcq
    apply hq
    apply hem
    funext x
    have h := hz x
    have h3 : (∑ q : (Σ a : A, Fin (n a)), ((em q.1 x - em a x) * c q) • fun s => ι (u q s)) = 0 := by
      have e1 : (M x).mulVec z
          = ∑ q : (Σ a : A, Fin (n a)), (em q.1 x * c q) • fun s => ι (u q s) := by
        rw [hc, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Matrix.mulVec_smul, hM, smul_smul, mul_comm]
      have e2 : em a x • z
          = ∑ q : (Σ a : A, Fin (n a)), (em a x * c q) • fun s => ι (u q s) := by
        rw [hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul]
      simp only [sub_mul, sub_smul, Finset.sum_sub_distrib]
      rw [← e1, ← e2, h, sub_self]
    have h4 := congrFun (hind _ h3) q
    simp only [Pi.zero_apply, mul_eq_zero] at h4
    exact sub_eq_zero.mp (h4.resolve_right hcq)
  refine ⟨fun i => c ⟨a, i⟩, ?_⟩
  rw [hc, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hzero ⟨a', i⟩ ha', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h
end GlobalTheory
