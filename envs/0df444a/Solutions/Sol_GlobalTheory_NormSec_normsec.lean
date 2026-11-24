-- Prove2me | solution 1 for GlobalTheory.NormSec.normsec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:28.734391+00:00
-- url     : https://prove2.me/submissions/2a46cd57-4cd2-442d-9712-b71ab8542486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactPreimageMulStarAnisotropicSubmoduleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitian
import Theorems.Thm_GlobalTheory_T_exists_isotropic_idempotent_centralizer_hermitian
import Theorems.Thm_GlobalTheory_T_isCompact_preimage_mul_star_anisotropic_submodule
import Theorems.Thm_GlobalTheory_T_matrix_commute_of_commute_separable_charpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NormSec
namespace GlobalTheory.NormSec
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  intro F E _ _ _ _ hU r A₀ hA hsep M hM
  classical
  have hA' : star A₀ = A₀ := by rw [Matrix.star_eq_conjTranspose]; exact hA
  obtain ⟨f, hfA, hff, hffs, haniso⟩ := GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian E r A₀ hA hsep
  have hcomm := GlobalTheory.T.matrix_commute_of_commute_separable_charpoly E r A₀ hsep
  have hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m := by
    intro m hm
    have := congrArg star hm
    rw [star_mul, star_mul, hA'] at this
    exact this.symm
  set g := star f with hg
  set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he
  have hes : star e = 1 - g - f := by rw [he, star_sub, star_sub, star_one, hg, star_star]
  let R := Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))
  have memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R := by
    intro m hm
    rw [Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hm.symm
  have memR' : ∀ m ∈ R, m * A₀ = A₀ * m := by
    intro m hm
    exact ((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm
  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }
  let V : Submodule E (Matrix (Fin r) (Fin r) E) :=
    { carrier := {z | z * A₀ = A₀ * z ∧ z * e = z}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }
  have hV : ∀ z ∈ V, z * star z = 0 → z = 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have h := haniso z hz1
    rw [hz2] at h
    exact h h0
  let M₁ := (fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M
  let M₂ := (fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M
  have hM₁ : IsCompact M₁ := hM.image Units.continuous_val
  have hM₂ : IsCompact M₂ := hM.image Units.continuous_coe_inv
  let B₁ := (fun x => x * e) '' M₁
  let B₂ := (fun x => x * e) '' M₂
  have hB₁ : IsCompact B₁ := hM₁.image (continuous_mul_right e)
  have hB₂ : IsCompact B₂ := hM₂.image (continuous_mul_right e)
  have hT₁ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₁ hB₁
  have hT₂ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₂ hB₂
  let P₁ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)
  let P₂ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)
  have hP₁ : IsCompact P₁ := (hT₁.prod hM₁).image (by fun_prop)
  have hP₂ : IsCompact P₂ := (hT₂.prod hM₂).image (by fun_prop)
  refine ⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩
  · have := Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hP₁.prod (hP₂.image MulOpposite.continuous_op))
    convert this using 1
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    rw [MulOpposite.op_injective.mem_set_image]
  rintro t ht ⟨m, hmM, hm⟩
  set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT
  set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi
  set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm
  set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi
  have cTi : Ti * A₀ = A₀ * Ti := Commute.units_inv_left (u := t) ht
  have cm : mm * A₀ = A₀ * mm := by
    rw [← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]
  have cmi : mi * A₀ = A₀ * mi := Commute.units_inv_left (u := m) cm
  let xT : R := ⟨T, memR _ ht⟩
  let xTp : R := ⟨star T, memR _ (hstarC _ ht)⟩
  let xTi : R := ⟨Ti, memR _ cTi⟩
  let xTip : R := ⟨star Ti, memR _ (hstarC _ cTi)⟩
  let xmi : R := ⟨mi, memR _ cmi⟩
  let xf : R := ⟨f, memR _ hfA⟩
  let xg : R := ⟨g, memR _ (hstarC _ hfA)⟩
  have hfR : xf * xf = xf := Subtype.ext hff
  have hgR : xg * xg = xg := Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])
  have hfgR : xf * xg = 0 := Subtype.ext hffs
  have hTiR : xT * xTi = 1 := Subtype.ext (Units.mul_inv t)
  have hTpiR : xTp * xTip = 1 := Subtype.ext (by
    show star T * star Ti = 1
    rw [← star_mul, hT, hTi, Units.inv_mul, star_one])
  have hmiR : xmi * (xT * xTp) = 1 := Subtype.ext (by
    show mi * (T * star T) = 1
    rw [hm, hmi, hmm, Units.inv_mul])
  have heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg := by linear_combination hfR + hgR + 2 * hfgR
  have hefR : (1 - xf - xg) * xf = 0 := by linear_combination -hfR - hfgR
  have hegR : (1 - xf - xg) * xg = 0 := by linear_combination -hgR - hfgR
  let X₀ : R := xT * (1 - xf - xg) + xT * xTp * xf + xg
  let X₁ : R := xTi * (1 - xf - xg) + xmi * xf + xg
  have h01 : X₀ * X₁ = 1 := by
    linear_combination (1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR +
      xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR
  have h10 : X₁ * X₀ = 1 := by rw [mul_comm]; exact h01
  let s : GL (Fin r) E := ⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩
  have hX₀ : X₀.1 = T * e + mm * f + g := by
    show T * (1 - f - g) + T * star T * f + g = _
    rw [hm]
  have hX₁ : X₁.1 = Ti * e + mi * f + g := rfl
  refine ⟨s, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩
    · exact memR' _ (xT * (1 - xf - xg)).2
    · have : xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg) := by linear_combination xT * heR
      exact congrArg Subtype.val this
    · refine ⟨mm, ⟨m, hmM, rfl⟩, ?_⟩
      have : xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp) := by
        linear_combination (-(xT * xTp)) * heR
      have h2 := congrArg Subtype.val this
      show mm * e = T * e * star (T * e)
      rw [star_mul, hes, ← hm]
      exact h2
  · refine ⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩
    · exact memR' _ (xTi * (1 - xf - xg)).2
    · have : xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg) := by linear_combination xTi * heR
      exact congrArg Subtype.val this
    · refine ⟨mi, ⟨m, hmM, rfl⟩, ?_⟩
      have hTT : xTi * xTip = xmi := by
        linear_combination (-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR
      have : xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip) := by
        linear_combination (-(xTi * xTip)) * heR - (1 - xf - xg) * hTT
      have h2 := congrArg Subtype.val this
      show mi * e = Ti * e * star (Ti * e)
      rw [star_mul, hes]
      exact h2
  · exact memR' _ X₀.2
  · have : X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp := by
      linear_combination xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR +
        xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR
    have h2 := congrArg Subtype.val this
    have hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1 := by
      show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f
      rw [hg]
      simp only [star_add, star_mul, star_sub, star_one, star_star]
    show X₀.1 * star X₀.1 = T * star T
    rw [hst]
    exact h2
end GlobalTheory.NormSec
