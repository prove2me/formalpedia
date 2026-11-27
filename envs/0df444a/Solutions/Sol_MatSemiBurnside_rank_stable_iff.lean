-- Prove2me | solution 1 for MatSemiBurnside.rank_stable_iff
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-27T00:41:41.099099+00:00
-- url     : https://prove2.me/submissions/b23de152-1523-4d10-91a8-da90cf6e4a57

import Mathlib
import Definitions.Def_MatSemiBurnside_IsStableSet

set_option autoImplicit false

open MatSemiBurnside

/-- The row action of `a * a` is the composition of the row action of `a` with itself. -/
lemma vecMulLin_sq {d : ℕ} (a : Matrix (Fin d) (Fin d) ℚ) :
    (a * a).vecMulLinear = a.vecMulLinear.comp a.vecMulLinear := by
  rw [← Matrix.mulVecLin_transpose, Matrix.transpose_mul, Matrix.mulVecLin_mul,
      Matrix.mulVecLin_transpose]

/-- The rank of `a` is the finrank of the range of the row action `a.vecMulLinear`. -/
lemma rank_glue {d : ℕ} (a : Matrix (Fin d) (Fin d) ℚ) :
    a.rank = Module.finrank ℚ (a.vecMulLinear.range) := by
  rw [← Matrix.rank_transpose, Matrix.rank, Matrix.mulVecLin_transpose]

namespace P2MHole01_bb3288ab
theorem solution {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] Fin d → ℚ) (H : f.ker ⊓ f.range = ⊥) (x : Fin d → ℚ)
  (hx : x ∈ f.range) (hx0 : f x = (0 : Fin d → ℚ)) : x = (0 : Fin d → ℚ) := by
  have hk : x ∈ f.ker := by rw [LinearMap.mem_ker]; exact hx0
  have hm : x ∈ f.ker ⊓ f.range := Submodule.mem_inf.mpr ⟨hk, hx⟩
  rw [H, Submodule.mem_bot] at hm
  exact hm
end P2MHole01_bb3288ab

/-- If the kernel and the image of `f` meet trivially, then `f` is injective on its image:
an element of the image killed by `f` lies in `ker f ⊓ range f = ⊥`. -/
lemma inter_bot_inj_on_range {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℚ))
    (H : f.ker ⊓ f.range = ⊥) (x : Fin d → ℚ) (hx : x ∈ f.range) (hx0 : f x = 0) :
    x = 0 := by
  (first | exact P2MHole01_bb3288ab.solution f H x hx hx0 | (apply P2MHole01_bb3288ab.solution <;> assumption))

namespace P2MHole02_bf2f382f
/- Hole 2 of rank_stable_iff: from ker(f) ∩ im(f) = {0} (written as H: x ∈ im f, f x = 0 → x = 0)
   conclude finrank (im (f ∘ₗ f)) = finrank (im f).
   Strategy: ker (f ∘ₗ f) = ker f, then cancel the kernel term in the two rank-nullity
   equations (LinearMap.finrank_range_add_finrank_ker). -/

theorem solution {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] Fin d → ℚ)
  (H : ∀ x ∈ f.range, f x = (0 : Fin d → ℚ) → x = (0 : Fin d → ℚ)) :
  Module.finrank ℚ ↥(f ∘ₗ f).range = Module.finrank ℚ ↥f.range := by
  have hk : (f ∘ₗ f).ker = f.ker := by
    ext x
    simp [LinearMap.comp_apply]
    constructor
    · intro hx
      exact H (f x) ⟨x, rfl⟩ hx
    · intro hx
      rw [hx]
      simp
  have nn1 : Module.finrank ℚ ↥(f ∘ₗ f).range + Module.finrank ℚ ↥(f ∘ₗ f).ker =
      Module.finrank ℚ (Fin d → ℚ) :=
    LinearMap.finrank_range_add_finrank_ker (f ∘ₗ f)
  have nn2 : Module.finrank ℚ ↥f.range + Module.finrank ℚ ↥f.ker =
      Module.finrank ℚ (Fin d → ℚ) :=
    LinearMap.finrank_range_add_finrank_ker f
  rw [hk] at nn1
  exact Nat.add_right_cancel (nn1.trans nn2.symm)
end P2MHole02_bf2f382f

-- riskiest
/-- If `f` is injective on its (finite-dimensional) image, then the restriction of `f` to
its image is an isomorphism onto its image, and the image of `f ∘ f` is the image of this
restriction, so the finrank of the image of `f ∘ f` equals the finrank of the image of `f`.
(Use `LinearMap.range_comp` for the image of `f ∘ f`; the inclusion in the image of `f`
follows from it as well.) -/
lemma inj_on_range_finrank_eq {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℚ))
    (H : ∀ (x : Fin d → ℚ), x ∈ f.range → f x = 0 → x = 0) :
    Module.finrank ℚ ((f.comp f).range) = Module.finrank ℚ (f.range) := by
  (first | exact P2MHole02_bf2f382f.solution f H | (apply P2MHole02_bf2f382f.solution <;> assumption))

namespace P2MHole03_bba85a40
/-- The image of `f ∘ₗ f` is contained in the image of `f`. -/
theorem hole3_dir1 {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] Fin d → ℚ) :
    (f ∘ₗ f).range ≤ f.range :=
  LinearMap.range_comp_le_range f f

theorem solution {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] Fin d → ℚ)
  (H : Module.finrank ℚ ↥(f ∘ₗ f).range = Module.finrank ℚ ↥f.range) : (f ∘ₗ f).range = f.range := by
  exact Submodule.eq_of_le_of_finrank_eq (hole3_dir1 f) H
end P2MHole03_bba85a40

/-- If the finrank of the image is stable under iteration, then the image of `f ∘ f` equals
the image of `f` (the inclusion of the image of `f ∘ f` in the image of `f`, which follows
from `LinearMap.range_comp`, plus monotonicity of `Module.finrank`). -/
lemma finrank_eq_comp_range {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℚ))
    (H : Module.finrank ℚ ((f.comp f).range) = Module.finrank ℚ (f.range)) :
    (f.comp f).range = f.range := by
  (first | exact P2MHole03_bba85a40.solution f H | (apply P2MHole03_bba85a40.solution <;> assumption))

namespace P2MHole04_3fa471ca
set_option maxHeartbeats 400000

/-- The kernel of `f` is contained in the kernel of `f ∘ f`:
- if `f x = 0` then `f (f x) = f 0 = 0`. -/
theorem ker_le_comp_ker {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] Fin d → ℚ) :
    f.ker ≤ (f.comp f).ker := by
  intro x hx
  have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
  have h : (f.comp f) x = 0 := by
    rw [LinearMap.comp_apply, hx0, LinearMap.map_zero]
  exact LinearMap.mem_ker.mpr h

theorem solution {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] Fin d → ℚ) (H : (f ∘ₗ f).range = f.range) :
  f.ker ⊓ f.range = ⊥ := by
  -- rank-nullity for `f` and for `f ∘ f` (V = Fin d → ℚ is finite-dimensional)
  have h_rn1 : Module.finrank ℚ (f.range) + Module.finrank ℚ (f.ker) = Module.finrank ℚ (Fin d → ℚ) :=
    LinearMap.finrank_range_add_finrank_ker f
  have h_rn2 : Module.finrank ℚ ((f.comp f).range) + Module.finrank ℚ ((f.comp f).ker) =
      Module.finrank ℚ (Fin d → ℚ) :=
    LinearMap.finrank_range_add_finrank_ker (f.comp f)
  -- H makes the two ranges equal, hence the two kernels have the same finrank
  have h_range : Module.finrank ℚ ((f.comp f).range) = Module.finrank ℚ (f.range) := by
    rw [H]
  have h_finrank_eq : Module.finrank ℚ (f.ker) = Module.finrank ℚ ((f.comp f).ker) := by
    rw [h_range] at h_rn2
    omega
  -- the inclusion plus equal finrank forces the kernels to be equal
  have h_ker_le : f.ker ≤ (f.comp f).ker := ker_le_comp_ker f
  have h_ker_eq : f.ker = (f.comp f).ker :=
    Submodule.eq_of_le_of_finrank_eq h_ker_le h_finrank_eq
  -- a vector in `f.ker ⊓ f.range` is zero
  apply le_antisymm
  · intro x hx
    have hx_ker : x ∈ f.ker := (Submodule.mem_inf.mp hx).1
    have hx_range : x ∈ f.range := (Submodule.mem_inf.mp hx).2
    obtain ⟨y, hy⟩ := Set.mem_range.mp hx_range
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx_ker
    have hy0 : (f.comp f) y = 0 := by
      rw [LinearMap.comp_apply, hy, hx0]
    have hy_ker : y ∈ f.ker := by
      rw [h_ker_eq]
      exact LinearMap.mem_ker.mpr hy0
    have hx0' : x = 0 := by
      rw [← hy]
      exact LinearMap.mem_ker.mp hy_ker
    simpa using hx0'
  · exact bot_le
end P2MHole04_3fa471ca

/-- If the image of `f ∘ f` equals the image of `f`, then the kernel and image of `f` meet
trivially: the restriction of `f` to its image is then surjective, hence injective on the
finite-dimensional image (rank–nullity), and its kernel is `ker f ⊓ range f`. -/
lemma comp_range_inter_bot {d : ℕ} (f : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℚ))
    (H : (f.comp f).range = f.range) :
    f.ker ⊓ f.range = ⊥ := by
  (first | exact P2MHole04_3fa471ca.solution f H | (apply P2MHole04_3fa471ca.solution <;> assumption))

/- **Rank-stable iff kernel and image meet trivially.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, Claim A.2 (last sentence),
p.29: "A matrix is rank-stable exactly when its kernel and image have intersection {0}."

**Formalization Note.** Row action kernel and image; `{0}` is the zero submodule `⊥`. -/
theorem solution {d : ℕ} (hd : 0 < d) (a : Matrix (Fin d) (Fin d) ℚ) :
    IsRankStable a ↔ rowKer a ⊓ rowIm a = ⊥ := by
  have hF : rowKer a ⊓ rowIm a = a.vecMulLinear.ker ⊓ a.vecMulLinear.range := by
    simp only [rowKer, rowIm]
  have hR : IsRankStable a ↔
      Module.finrank ℚ (a.vecMulLinear.range) =
        Module.finrank ℚ ((a.vecMulLinear.comp a.vecMulLinear).range) := by
    unfold IsRankStable
    rw [rank_glue, rank_glue (a ^ 2), pow_two, vecMulLin_sq]
  rw [hR]
  refine ⟨?_, ?_⟩
  · intro H
    rw [hF]
    exact comp_range_inter_bot a.vecMulLinear (finrank_eq_comp_range a.vecMulLinear H.symm)
  · intro H
    rw [hF] at H
    exact (inj_on_range_finrank_eq a.vecMulLinear (inter_bot_inj_on_range a.vecMulLinear H)).symm
