-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.exists_mem_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:30.997081+00:00
-- url     : https://prove2.me/submissions/7fadd76b-8f11-492c-b2f8-33c1bb177bc8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_det_gramOf_ne_zero
import Theorems.Thm_GlobalTheory_BoundedBasis_herm_vecMul
import Theorems.Thm_GlobalTheory_BoundedBasis_exists_vecMul_eq
import Theorems.Thm_GlobalTheory_BoundedBasis_exists_gl_mulVec
import Theorems.Thm_GlobalTheory_BoundedBasis_coe_pairing
import Theorems.Thm_GlobalTheory_BoundedBasis_smul_vecMul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {v w : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hw : ∀ i, w i ∈ X.L') (hvi : LinearIndependent E v) (hwi : LinearIndependent E w)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) (hvA : gramOf X.Gm v = A.map (algebraMap (𝓞 E) E))
    (hwA : gramOf X.Gm w = A.map (algebraMap (𝓞 E) E))
    (h : ∀ x : X.Λ, pairing X w hw x - pairing X v hv x ∈
      LinearMap.range (((X.NA * X.NC * X.g : ℕ) : 𝓞 E) • A).vecMulLinear) :
    ∃ γ ∈ X.Γ, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i := by
  obtain ⟨γ, hγ⟩ := exists_gl_mulVec hvi hwi
  have key : ∀ x ∈ X.Λ, ∀ c d : Fin r → E, x = c ᵥ* Matrix.of v → x = d ᵥ* Matrix.of w →
      ∃ o : Fin r → 𝓞 E, d = c + (X.g : E) • (X.NC : E) • fun i => (o i : E) := by
    intro x hx c d hc hd
    obtain ⟨o, ho⟩ := h ⟨x, hx⟩
    refine ⟨o, ?_⟩
    have h1 : ((X.NA : E) • (d - (c + (X.g : E) • (X.NC : E) • fun i => (o i : E)))) ᵥ*
        gramOf X.Gm v = 0 := by
      funext k
      have h2 := congrArg (algebraMap (𝓞 E) E) (congrFun ho k)
      have h3 := coe_pairing X v hv ⟨x, hx⟩ c hc k
      have h4 := coe_pairing X w hw ⟨x, hx⟩ d hd k
      rw [hwA, ← hvA] at h4
      rw [Pi.sub_apply, map_sub] at h2
      change _ = ((pairing X w hw ⟨x, hx⟩ k : 𝓞 E) : E) - (pairing X v hv ⟨x, hx⟩ k : 𝓞 E) at h2
      rw [h3, h4] at h2
      rw [smul_sub, smul_add, sub_vecMul, add_vecMul, Pi.sub_apply, Pi.add_apply, ← sub_sub, ← h2,
        hvA]
      simp only [vecMulLinear_apply, vecMul, dotProduct, map_sum, Matrix.smul_apply, smul_eq_mul,
        map_mul, map_natCast, Pi.smul_apply, map_apply, Pi.zero_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      push_cast
      ring
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hvi) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_left (by exact_mod_cast X.NA_pos.ne'))
  have hg : ∀ y ∈ X.Λ, (X.g : E) • y ∈ X.Λ := fun y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
  have hcong : ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (X.g : E) • y := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_vecMul_eq hvi x
    obtain ⟨d, hd⟩ := exists_vecMul_eq hwi x
    obtain ⟨o, ho⟩ := key x hx c d hc hd
    refine ⟨_, smul_vecMul_mem X hv o, ?_⟩
    have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = d ᵥ* Matrix.of v := by rw [hd, hγ]
    rw [this, ho, add_vecMul, ← hc, smul_vecMul, smul_vecMul, add_sub_cancel_left]
  refine ⟨γ, X.cong γ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ hcong, fun i => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_vecMul_eq hwi x
    obtain ⟨d, rfl⟩ := exists_vecMul_eq hwi y
    rw [hγ, hγ, herm_vecMul, herm_vecMul, hvA, hwA]
  · obtain ⟨y, hy, h⟩ := hcong x hx
    rw [sub_eq_iff_eq_add.1 h]
    exact add_mem (hg y hy) hx
  · obtain ⟨c, rfl⟩ := exists_vecMul_eq hwi x
    obtain ⟨d, hd⟩ := exists_vecMul_eq hwi ((γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w))
    obtain ⟨o, ho⟩ := key _ hx c d (hγ c) hd
    rw [hd, ho, add_vecMul, smul_vecMul, smul_vecMul] at hx
    exact (Submodule.add_mem_iff_left _ (hg _ (smul_vecMul_mem X hw o))).1 hx
  · have := hγ (Pi.single i 1)
    rw [single_one_vecMul, single_one_vecMul] at this
    exact this.symm
end GlobalTheory.BoundedBasis
