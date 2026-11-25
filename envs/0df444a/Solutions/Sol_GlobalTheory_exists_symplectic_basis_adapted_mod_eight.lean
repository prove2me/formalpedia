-- Prove2me | solution 1 for GlobalTheory.exists_symplectic_basis_adapted_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:06.299503+00:00
-- url     : https://prove2.me/submissions/2650f2e2-a2b2-4072-9695-4b328a0b494b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Theorems.Thm_GlobalTheory_datum_free_int
import Theorems.Thm_GlobalTheory_datum_finrank_int
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_bijective_neg_bilinForm
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_adapted_dvd
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma w0_sq_eq_w0_sub_two_mul (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 ^ 2 = H.w0 - 2 * ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E) := by
  have hd : (H.d : 𝓞 E) = 16 * ((H.d / 16 : ℕ) : 𝓞 E) + 7 := by
    have := Nat.div_add_mod H.d 16
    rw [H.d_mod] at this
    exact_mod_cast this.symm
  have h4 : (4 : 𝓞 E) * (H.w0 ^ 2 - (H.w0 - 2 * ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E))) = 0 := by
    push_cast
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hd
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · exact sub_eq_zero.mp h
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma host_bar_rt_eq_neg (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    simpa using congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hconj : (starRingEnd ℂ) (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E) with hz
    have hre := congrArg Complex.re hsq
    have him := congrArg Complex.im hsq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
    have hre0 : z.re = 0 := by
      rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · rw [h] at hre; nlinarith [sq_nonneg z.re]
      · norm_num at h
    apply Complex.ext <;> simp [hre0]
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, NumberField.IsCMField.complexEmbedding_complexConj, hconj]
  simp
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma host_bar_w0 (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, host_bar_rt_eq_neg, map_ofNat] at h
  have h2 : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0 := by
    linear_combination h + H.two_weight_eq_one_add_root
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact sub_eq_zero.mp h3
end GlobalTheory
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ),
      g = Module.finrank ℚ E / 2 * (D.p + D.q) → ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La),
        (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
        (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧
        (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) := by
  intro E _ _ _ H D g hg
  haveI := D.fin
  haveI : Module.Free ℤ D.La := _root_.GlobalTheory.datum_free_int D
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  set w := H.w0 with hw
  set m : 𝓞 E := ((2 * (H.d / 16 : ℕ) + 1 : ℕ) : 𝓞 E) with hm
  have hsq : w ^ 2 = w - 2 * m := w0_sq_eq_w0_sub_two_mul H
  have hA : w ^ 4 + (1 - w) ^ 4 = 1 + 8 * (m ^ 2 - m) := by
    linear_combination (2 * w ^ 2 - 2 * w + 4 - 4 * m) * hsq
  have hB : w ^ 4 * (1 - w) ^ 4 = 8 * (2 * m ^ 4) := by
    have h : w * (1 - w) = 2 * m := by linear_combination -hsq
    rw [← mul_pow, h]; ring
  have hC : w ^ 4 * w ^ 4 = w ^ 4 + 8 * ((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) := by
    linear_combination w ^ 4 * hA - hB
  have hbar4 : H.bar (w ^ 4) = (1 - w) ^ 4 := by rw [map_pow, hw, host_bar_w0]
  have hbar4' : H.bar ((1 - w) ^ 4) = w ^ 4 := by
    rw [map_pow, map_sub, map_one, hw, host_bar_w0]; ring
  have h8 : ∀ u : D.La, (8 : 𝓞 E) • u = (8 : ℤ) • u := fun u => by
    simpa using Int.cast_smul_eq_zsmul (𝓞 E) (8 : ℤ) u
  have hn8 : ∀ u : D.La, (8 : ℕ) • u = (8 : 𝓞 E) • u := fun u => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; norm_num
  have hE8 : ∀ u v : D.La, D.EF ((8 : 𝓞 E) • u) v = 8 * D.EF u v := fun u v => by
    rw [h8, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hE8' : ∀ u v : D.La, D.EF u ((8 : 𝓞 E) • v) = 8 * D.EF u v := fun u v => by
    rw [h8, map_smul, smul_eq_mul]
  let P : Submodule ℤ D.La :=
    { carrier := {x | ∃ e, w ^ 4 • x = x + (8 : 𝓞 E) • e}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [smul_add, ha, hb, smul_add]; abel⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨c • a, by rw [smul_comm (w ^ 4) c x, ha, smul_add, smul_comm c (8 : 𝓞 E) a]⟩ }
  let Q : Submodule ℤ D.La :=
    { carrier := {x | ∃ e, w ^ 4 • x = (8 : 𝓞 E) • e}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [smul_add, ha, hb, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨c • a, by rw [smul_comm (w ^ 4) c x, ha, smul_comm c (8 : 𝓞 E) a]⟩ }
  have hP8 : ∀ x : D.La, ((8 : ℕ) : ℤ) • x ∈ P := fun x =>
    ⟨w ^ 4 • x - x, by
      rw [show ((8 : ℕ) : ℤ) = 8 by norm_num, ← h8, smul_comm (w ^ 4) (8 : 𝓞 E) x, smul_sub]
      abel⟩
  have hQ8 : ∀ x : D.La, ((8 : ℕ) : ℤ) • x ∈ Q := fun x =>
    ⟨w ^ 4 • x, by rw [show ((8 : ℕ) : ℤ) = 8 by norm_num, ← h8, smul_comm (w ^ 4) (8 : 𝓞 E) x]⟩
  have hPiso : ∀ x ∈ P, ∀ y ∈ P, (8 : ℤ) ∣ D.EF x y := by
    rintro x ⟨a, ha⟩ y ⟨b, hb⟩
    have hy : (1 - w) ^ 4 • y = (8 : 𝓞 E) • ((2 * m ^ 4) • y - (1 - w) ^ 4 • b) := by
      calc (1 - w) ^ 4 • y = (1 - w) ^ 4 • (w ^ 4 • y - (8 : 𝓞 E) • b) := by
            rw [hb, add_sub_cancel_right]
        _ = ((1 - w) ^ 4 * w ^ 4) • y - ((1 - w) ^ 4 * 8) • b := by
            rw [smul_sub, smul_smul, smul_smul]
        _ = (8 * (2 * m ^ 4)) • y - (8 * (1 - w) ^ 4) • b := by
            rw [mul_comm ((1 - w) ^ 4) (w ^ 4), hB, mul_comm ((1 - w) ^ 4) 8]
        _ = (8 : 𝓞 E) • ((2 * m ^ 4) • y - (1 - w) ^ 4 • b) := by
            simp only [smul_sub, mul_smul]
    have hx : D.EF x y = D.EF (w ^ 4 • x) y - 8 * D.EF a y := by
      rw [ha, map_add, LinearMap.add_apply, hE8]; ring
    rw [hx, D.adj, hbar4, hy, hE8']
    exact (dvd_mul_right _ _).sub (dvd_mul_right _ _)
  have hQiso : ∀ x ∈ Q, ∀ y ∈ Q, (8 : ℤ) ∣ D.EF x y := by
    rintro x ⟨a, ha⟩ y ⟨b, hb⟩
    have hx : x = (8 : 𝓞 E) • (a - (m ^ 2 - m) • x) + (1 - w) ^ 4 • x := by
      calc x = (1 : 𝓞 E) • x := (one_smul _ _).symm
        _ = (w ^ 4 + (1 - w) ^ 4 - 8 * (m ^ 2 - m)) • x := by
            congr 1; linear_combination -hA
        _ = w ^ 4 • x + (1 - w) ^ 4 • x - (8 * (m ^ 2 - m)) • x := by
            rw [sub_smul, add_smul]
        _ = (8 : 𝓞 E) • (a - (m ^ 2 - m) • x) + (1 - w) ^ 4 • x := by
            rw [ha, mul_smul, smul_sub]; abel
    have hxy : D.EF x y = 8 * D.EF (a - (m ^ 2 - m) • x) y + D.EF ((1 - w) ^ 4 • x) y := by
      conv_lhs => rw [hx]
      rw [map_add, LinearMap.add_apply, hE8]
    rw [hxy, D.adj, hbar4', hb, hE8']
    exact (dvd_mul_right _ _).add (dvd_mul_right _ _)
  have hsup : P ⊔ Q = ⊤ := by
    refine eq_top_iff.mpr fun x _ => Submodule.mem_sup.mpr ⟨w ^ 4 • x, ?_, x - w ^ 4 • x, ?_, ?_⟩
    · exact ⟨((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) • x, by
        rw [smul_smul, hC, add_smul, mul_smul]⟩
    · exact ⟨-(((m ^ 2 - m) * w ^ 4 - 2 * m ^ 4) • x), by
        rw [smul_sub, smul_smul, hC, add_smul, mul_smul, smul_neg]; abel⟩
    · abel
  have halt : (-D.EF).IsAlt := fun x => by simp [D.alt]
  have hfin : Module.finrank ℤ D.La = 2 * g := by
    rw [hg]; exact _root_.GlobalTheory.datum_finrank_int D
  obtain ⟨c, hc, hcP, hcQ⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_adapted_dvd halt
    (_root_.GlobalTheory.bijective_neg_bilinForm D.unimod) hfin (N := 8) (by norm_num) hP8 hQ8
    (fun x hx y hy => by simpa using hPiso x hx y hy)
    (fun x hx y hy => by simpa using hQiso x hx y hy) hsup
  have hrepr : ∀ a j, c.repr (c.equivFun.symm a) j = a j := fun a j => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hsingle : ∀ i, c.equivFun.symm (Pi.single i 1) = c i := fun i => by simp
  refine ⟨c.equivFun.symm, fun a b => ?_, fun k => ?_, fun k => ?_⟩
  · have h := hc.apply_eq_sum halt (c.equivFun.symm a) (c.equivFun.symm b)
    simp only [hrepr, LinearMap.neg_apply] at h
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
    rw [← h, neg_neg]
  · rw [hsingle]
    obtain ⟨e, he⟩ := (hcP (c (Sum.inl k))).mpr fun i => by simp
    exact ⟨e, by rw [he, hn8]⟩
  · rw [hsingle]
    obtain ⟨e, he⟩ := (hcQ (c (Sum.inr k))).mpr fun i => by simp
    exact ⟨e, by rw [he, hn8]⟩
end _root_.GlobalTheory
end GlobalTheory
