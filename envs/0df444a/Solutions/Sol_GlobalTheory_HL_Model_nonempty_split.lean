-- Prove2me | solution 1 for GlobalTheory.HL.Model.nonempty_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:22.459522+00:00
-- url     : https://prove2.me/submissions/19c3638b-31dd-4475-b856-69d2f68649c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_exists_char
import Theorems.Thm_GlobalTheory_HL_Model_isIntegral_iff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution [IsNonarchimedeanLocalField F] :
    ∃ L : LocE F (F × F), (∀ x, L.cj x = x.swap) ∧ L.O = (𝒪[F]).prod 𝒪[F] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])
  have hϖ0 : (ϖ : F) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have hinv : (ϖ : F)⁻¹ ∉ 𝒪[F] := by
    intro h
    apply hϖ.not_isUnit
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext (by simp [hϖ0])⟩
  obtain ⟨ψ, hψo, hψ⟩ := exists_char _ hinv
  have hcont : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hO : (𝒪[F] : Set F) ∈ nhds (0 : F) :=
      (Valuation.isOpen_integer (v := ValuativeRel.valuation F)).mem_nhds (zero_mem _)
    have ht : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
      rw [← sub_self x]
      exact Filter.tendsto_id.sub tendsto_const_nhds
    have hev : ∀ᶠ y in nhds x, ψ x = ψ y := by
      filter_upwards [ht hO] with y hy
      have hy' : y = x + (y - x) := by ring
      rw [hy', AddChar.map_add_eq_mul, hψo _ hy, mul_one]
    exact continuousAt_const.congr hev
  have key : ∀ b : F, b ∉ 𝒪[F] → ∃ t ∈ 𝒪[F], b * t = (ϖ : F)⁻¹ := by
    intro b hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hb (zero_mem _)
    have hlt : ValuativeRel.valuation F b⁻¹ < 1 :=
      (Valuation.one_lt_val_iff _ hb0).mp (not_le.mp fun h => hb h)
    have hbi : b⁻¹ ∈ 𝒪[F] := hlt.le
    have hnu : ¬ IsUnit (⟨b⁻¹, hbi⟩ : 𝒪[F]) := fun hu =>
      hlt.ne ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mp hu)
    have hmem : (⟨b⁻¹, hbi⟩ : 𝒪[F]) ∈ Ideal.span {ϖ} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hs' : (s : F) * ϖ = b⁻¹ := congrArg Subtype.val hs
    refine ⟨s, s.2, ?_⟩
    calc b * (s : F) = b * ((s : F) * ϖ) * (ϖ : F)⁻¹ := by field_simp
      _ = (ϖ : F)⁻¹ := by rw [hs', mul_inv_cancel₀ hb0, one_mul]
  let O : Subring (F × F) := (𝒪[F]).prod 𝒪[F]
  have memO : ∀ x : F × F, x ∈ O ↔ x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F] := fun x => Subring.mem_prod
  have comp : ∀ (p : 𝒪[F]), Irreducible p → ∀ a ra : F, a ∈ 𝒪[F] → ra ∈ 𝒪[F] →
      ra * p = a * a → ∃ s ∈ 𝒪[F], s * p = a := by
    intro p hp a ra ha hra h
    have hdvd : p ∣ (⟨a, ha⟩ : 𝒪[F]) * ⟨a, ha⟩ :=
      ⟨⟨ra, hra⟩, Subtype.ext (by push_cast; rw [← h, mul_comm])⟩
    obtain ⟨s, hs⟩ := (hp.prime.dvd_or_dvd hdvd).elim id id
    refine ⟨s, s.2, ?_⟩
    have hs' := congrArg Subtype.val hs
    push_cast at hs'
    rw [hs', mul_comm]
  let sw : (F × F) ≃ₐ[F] (F × F) :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  refine ⟨{
    cj := sw
    cj_cj := fun x => rfl
    cj_fix := fun x => by
      constructor
      · intro h
        have h2 : x.2 = x.1 := congrArg Prod.fst h
        exact ⟨x.1, Prod.ext rfl h2.symm⟩
      · rintro ⟨a, rfl⟩
        rfl
    free := inferInstance
    rank := by simp
    reduced := inferInstance
    top := inferInstance
    O := O
    O_def := fun x => by
      rw [memO, ← GlobalTheory.HL.Model.isIntegral_iff x.1, ← GlobalTheory.HL.Model.isIntegral_iff x.2]
      exact IsIntegral.pair_iff.symm
    unram := fun p hp x hx hxx => by
      rw [Submodule.mem_span_singleton] at hxx ⊢
      obtain ⟨r, hr⟩ := hxx
      have hr1 : r.1.1 * p = x.1 * x.1 := by
        have := congrArg Prod.fst hr
        simpa [Subring.smul_def] using this
      have hr2 : r.1.2 * p = x.2 * x.2 := by
        have := congrArg Prod.snd hr
        simpa [Subring.smul_def] using this
      obtain ⟨s1, hs1, e1⟩ := comp p hp x.1 r.1.1 ((memO x).mp hx).1 ((memO _).mp r.2).1 hr1
      obtain ⟨s2, hs2, e2⟩ := comp p hp x.2 r.1.2 ((memO x).mp hx).2 ((memO _).mp r.2).2 hr2
      refine ⟨⟨(s1, s2), (memO _).mpr ⟨hs1, hs2⟩⟩, Prod.ext ?_ ?_⟩
      · simpa [Subring.smul_def] using e1
      · simpa [Subring.smul_def] using e2
    psi0 := { toFun := fun x => ψ (x.1 + x.2)
              map_zero_eq_one' := by simp
              map_add_eq_mul' := fun x y => by
                simp only [Prod.fst_add, Prod.snd_add]
                rw [add_add_add_comm, AddChar.map_add_eq_mul] }
    local_additive_char_continuous := hcont.comp (continuous_fst.add continuous_snd)
    local_additive_char_conj := fun y => by
      show ψ (y.2 + y.1) = ψ (y.1 + y.2)
      rw [add_comm]
    additive_character_dual_ring := fun x => by
      constructor
      · intro h
        rw [memO]
        constructor
        · by_contra h1
          obtain ⟨t, ht, hbt⟩ := key _ h1
          have h2 := h (t, 0) ((memO _).mpr ⟨ht, zero_mem _⟩)
          change ψ ((x * (t, 0)).1 + (x * (t, 0)).2) = 1 at h2
          simp only [Prod.fst_mul, Prod.snd_mul, mul_zero, add_zero, hbt] at h2
          exact hψ h2
        · by_contra h1
          obtain ⟨t, ht, hbt⟩ := key _ h1
          have h2 := h (0, t) ((memO _).mpr ⟨zero_mem _, ht⟩)
          change ψ ((x * (0, t)).1 + (x * (0, t)).2) = 1 at h2
          simp only [Prod.fst_mul, Prod.snd_mul, mul_zero, zero_add, hbt] at h2
          exact hψ h2
      · intro hx y hy
        have hxy := (memO _).mp (O.mul_mem hx hy)
        exact hψo _ (add_mem hxy.1 hxy.2) }, fun x => rfl, rfl⟩
end GlobalTheory.HL.Model
