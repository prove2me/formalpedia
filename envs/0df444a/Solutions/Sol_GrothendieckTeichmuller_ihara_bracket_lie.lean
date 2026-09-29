-- Prove2me | solution 1 for GrothendieckTeichmuller.ihara_bracket_lie
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T05:43:09.633825+00:00
-- url     : https://prove2.me/submissions/4b9483c1-883d-4065-bed3-b182c1c08889

import Definitions.Def_GT_grt1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open GrothendieckTeichmuller

/-!
# The Ihara bracket makes the free Lie algebra a Lie algebra

Mathlib has neither the Grothendieck-Teichmuller Lie algebra nor the Ihara bracket; the
extensionality principle for derivations of a free Lie algebra is built here in a private
namespace.
-/

namespace IharaAux


theorem bracket_gx_gy : iharaBracket gx gy = 0 := by
  rw [iharaBracket, iharaDeriv_gy, iharaDeriv_gx, sub_zero, ← lie_skew, neg_add_cancel]

/-- The graph of a derivation, as a Lie algebra morphism into the semidirect product. -/
noncomputable def derivHom (D : LieDerivation ℚ Lxy Lxy) : Lxy →ₗ⁅ℚ⁆ AdExt where
  toFun u := ((⟨u, D u⟩ : Lxy × Lxy) : AdExt)
  map_add' u v := by
    refine AdExt.ext' rfl ?_
    exact map_add D u v
  map_smul' c u := by
    refine AdExt.ext' rfl ?_
    exact map_smul D c u
  map_lie' := by
    intro u v
    refine AdExt.ext' rfl ?_
    exact LieDerivation.apply_lie_eq_sub D u v

/-- Two derivations of the free Lie algebra on `x`, `y` agreeing on the generators are equal. -/
theorem deriv_ext {D E : LieDerivation ℚ Lxy Lxy} (hx : D gx = E gx) (hy : D gy = E gy) :
    D = E := by
  have h : derivHom D = derivHom E := by
    refine FreeLieAlgebra.hom_ext ?_
    intro i
    fin_cases i
    · exact AdExt.ext' rfl hx
    · exact AdExt.ext' rfl hy
  ext u
  exact congrArg (fun φ : Lxy →ₗ⁅ℚ⁆ AdExt => (AdExt.toPair (φ u)).2) h

theorem deriv_commutator (f g : Lxy) :
    ⁅iharaDeriv f, iharaDeriv g⁆ =
      iharaDeriv ⁅f, g⁆ + iharaDeriv (iharaDeriv f g) - iharaDeriv (iharaDeriv g f) := by
  refine deriv_ext ?_ ?_
  · rw [LieDerivation.commutator_apply, iharaDeriv_gx, iharaDeriv_gx]
    simp only [LieDerivation.sub_apply, LieDerivation.add_apply, iharaDeriv_gx, map_zero]
    abel
  · rw [LieDerivation.commutator_apply, iharaDeriv_gy, iharaDeriv_gy]
    rw [LieDerivation.apply_lie_eq_sub (iharaDeriv f) gy g,
      LieDerivation.apply_lie_eq_sub (iharaDeriv g) gy f,
      iharaDeriv_gy, iharaDeriv_gy]
    simp only [LieDerivation.sub_apply, LieDerivation.add_apply, iharaDeriv_gy]
    rw [leibniz_lie gy f g, ← lie_skew ⁅gy, f⁆ g]
    abel

theorem deriv_add (f g : Lxy) : iharaDeriv (f + g) = iharaDeriv f + iharaDeriv g := by
  refine deriv_ext ?_ ?_
  · rw [iharaDeriv_gx, LieDerivation.add_apply, iharaDeriv_gx, iharaDeriv_gx, add_zero]
  · rw [iharaDeriv_gy, LieDerivation.add_apply, iharaDeriv_gy, iharaDeriv_gy, lie_add]

theorem deriv_sub (f g : Lxy) : iharaDeriv (f - g) = iharaDeriv f - iharaDeriv g := by
  refine deriv_ext ?_ ?_
  · rw [iharaDeriv_gx, LieDerivation.sub_apply, iharaDeriv_gx, iharaDeriv_gx, sub_zero]
  · rw [iharaDeriv_gy, LieDerivation.sub_apply, iharaDeriv_gy, iharaDeriv_gy, lie_sub]

theorem deriv_smul (c : ℚ) (f : Lxy) : iharaDeriv (c • f) = c • iharaDeriv f := by
  refine deriv_ext ?_ ?_
  · rw [iharaDeriv_gx, LieDerivation.smul_apply, iharaDeriv_gx, smul_zero]
  · rw [iharaDeriv_gy, LieDerivation.smul_apply, iharaDeriv_gy, lie_smul]

theorem deriv_bracket (f g : Lxy) :
    iharaDeriv (iharaBracket f g) = ⁅iharaDeriv f, iharaDeriv g⁆ := by
  rw [iharaBracket, deriv_sub, deriv_add, deriv_commutator]

theorem bracket_skew (f g : Lxy) : iharaBracket f g = -iharaBracket g f := by
  have hs : ⁅g, f⁆ = -⁅f, g⁆ := by
    rw [← lie_skew f g]
    abel
  rw [iharaBracket, iharaBracket, hs]
  abel

theorem bracket_add (f g h : Lxy) :
    iharaBracket (f + g) h = iharaBracket f h + iharaBracket g h := by
  rw [iharaBracket, iharaBracket, iharaBracket, add_lie, deriv_add,
    LieDerivation.add_apply, map_add]
  abel

theorem bracket_smul (c : ℚ) (f g : Lxy) :
    iharaBracket (c • f) g = c • iharaBracket f g := by
  rw [iharaBracket, iharaBracket, smul_lie, deriv_smul, LieDerivation.smul_apply, map_smul,
    smul_sub, smul_add]

theorem bracket_expand (a b c : Lxy) :
    iharaBracket a (iharaBracket b c)
      = ⁅a, ⁅b, c⁆⁆ + (⁅a, iharaDeriv b c⁆ - ⁅a, iharaDeriv c b⁆)
        + (⁅b, iharaDeriv a c⁆ - ⁅c, iharaDeriv a b⁆)
        + (iharaDeriv a (iharaDeriv b c) - iharaDeriv a (iharaDeriv c b))
        - (iharaDeriv b (iharaDeriv c a) - iharaDeriv c (iharaDeriv b a)) := by
  have hD : iharaDeriv (iharaBracket b c) a
      = iharaDeriv b (iharaDeriv c a) - iharaDeriv c (iharaDeriv b a) := by
    rw [deriv_bracket, LieDerivation.commutator_apply]
  rw [iharaBracket, hD]
  rw [show iharaBracket b c = ⁅b, c⁆ + iharaDeriv b c - iharaDeriv c b from rfl]
  rw [lie_sub, lie_add, map_sub, map_add]
  rw [LieDerivation.apply_lie_eq_sub (iharaDeriv a) b c]
  abel

theorem bracket_jacobi (f g h : Lxy) :
    iharaBracket f (iharaBracket g h) + iharaBracket g (iharaBracket h f)
      + iharaBracket h (iharaBracket f g) = 0 := by
  have hjac : ⁅f, ⁅g, h⁆⁆ + ⁅g, ⁅h, f⁆⁆ + ⁅h, ⁅f, g⁆⁆ = 0 := by
    have h1 := leibniz_lie f g h
    have h2 : ⁅g, ⁅h, f⁆⁆ = -⁅g, ⁅f, h⁆⁆ := by
      rw [show ⁅h, f⁆ = -⁅f, h⁆ from by rw [← lie_skew f h]; abel, lie_neg]
    have h3 : ⁅h, ⁅f, g⁆⁆ = -⁅⁅f, g⁆, h⁆ := by
      rw [← lie_skew ⁅f, g⁆ h]
      abel
    rw [h1, h2, h3]
    abel
  have hB : ⁅g, ⁅h, f⁆⁆ = -⁅f, ⁅g, h⁆⁆ - ⁅h, ⁅f, g⁆⁆ := by
    have hre : ⁅g, ⁅h, f⁆⁆
        = (⁅f, ⁅g, h⁆⁆ + ⁅g, ⁅h, f⁆⁆ + ⁅h, ⁅f, g⁆⁆) - ⁅f, ⁅g, h⁆⁆ - ⁅h, ⁅f, g⁆⁆ := by
      abel
    rw [hre, hjac]
    abel
  rw [bracket_expand f g h, bracket_expand g h f, bracket_expand h f g, hB]
  abel

theorem bracket_lie :
    (∀ f g h : Lxy, iharaBracket (f + g) h = iharaBracket f h + iharaBracket g h) ∧
    (∀ (c : ℚ) (f g : Lxy), iharaBracket (c • f) g = c • iharaBracket f g) ∧
    (∀ f g : Lxy, iharaBracket f g = -iharaBracket g f) ∧
    (∀ f g h : Lxy, iharaBracket f (iharaBracket g h) + iharaBracket g (iharaBracket h f) +
      iharaBracket h (iharaBracket f g) = 0) :=
  ⟨bracket_add, bracket_smul, bracket_skew, bracket_jacobi⟩


end IharaAux

theorem solution :
    (∀ f g h : GrothendieckTeichmuller.Lxy,
        GrothendieckTeichmuller.iharaBracket (f + g) h
          = GrothendieckTeichmuller.iharaBracket f h + GrothendieckTeichmuller.iharaBracket g h) ∧
    (∀ (c : ℚ) (f g : GrothendieckTeichmuller.Lxy),
        GrothendieckTeichmuller.iharaBracket (c • f) g
          = c • GrothendieckTeichmuller.iharaBracket f g) ∧
    (∀ f g : GrothendieckTeichmuller.Lxy,
        GrothendieckTeichmuller.iharaBracket f g
          = -GrothendieckTeichmuller.iharaBracket g f) ∧
    (∀ f g h : GrothendieckTeichmuller.Lxy,
        GrothendieckTeichmuller.iharaBracket f (GrothendieckTeichmuller.iharaBracket g h) +
          GrothendieckTeichmuller.iharaBracket g (GrothendieckTeichmuller.iharaBracket h f) +
          GrothendieckTeichmuller.iharaBracket h (GrothendieckTeichmuller.iharaBracket f g) = 0) :=
  IharaAux.bracket_lie
