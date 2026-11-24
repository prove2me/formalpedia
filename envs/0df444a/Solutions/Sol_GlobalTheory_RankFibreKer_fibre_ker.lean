-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.fibre_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:51:31.264874+00:00
-- url     : https://prove2.me/submissions/8511907c-594d-4ecb-bf9b-672c2f7a4500

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFirstMaximalMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSliceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstMaximalMinorLocallyConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionMeasureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceSectionHaarDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarIntegralOverCosetRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariants
import Theorems.Thm_GlobalTheory_RankFibreKer_continuousOn_sec
import Theorems.Thm_GlobalTheory_RankFibreKer_sec_mem_slice
import Theorems.Thm_GlobalTheory_RankFibreKer_vol_ne_zero
import Theorems.Thm_GlobalTheory_RankFibreKer_tw_mul
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
import Theorems.Thm_GlobalTheory_T_coinvariant_of_locally_constant_twist
import Theorems.Thm_GlobalTheory_T_compact_covered_by_open_cosets
import Theorems.Thm_GlobalTheory_T_continuous_slice_section_integral
import Theorems.Thm_GlobalTheory_T_continuous_slice_section_measure
import Theorems.Thm_GlobalTheory_T_full_rank_iff_nonzero_minor
import Theorems.Thm_GlobalTheory_T_haar_integral_over_coset_representatives
import Theorems.Thm_GlobalTheory_T_isLocallyConstant_indicator_mul_slice
import Theorems.Thm_GlobalTheory_T_orbital_integral_vanishes_of_fibre
import Theorems.Thm_GlobalTheory_T_slice_stabilizer_trivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RankFibreKer
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b),
    GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  intro k _ _ _ _ _ _ a b ν β hν _ Φ hΦ hfib
  have hun : ∀ (Z : Matrix (Fin a) (Fin (a + b)) k) (g : GL (Fin a) k), Z ∈ slice k a (a + b) →
      g.val * Z ∈ slice k a (a + b) → g = 1 := GlobalTheory.T.slice_stabilizer_trivial k a (a + b)
  have hsc := continuousOn_sec (k := k) (a := a) (d := a + b)
  have hsl := sec_mem_slice (k := k) (a := a) (d := a + b)
  obtain ⟨U, hU, hUf⟩ := GlobalTheory.T.continuous_slice_section_integral k a (a + b) Φ hΦ sec hsc hsl hun
  let Kf : Subgroup (GL (Fin a) k) :=
    { carrier := {x | ∀ g : GL (Fin a) k, ∀ Z ∈ slice k a (a + b), Φ (g.val * x.val * Z) = Φ (g.val * Z)}
      one_mem' := fun g Z _ => by simp
      mul_mem' := fun {x y} hx hy g Z hZ => by
        rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, hy (g * x) Z hZ, Units.val_mul, hx g Z hZ]
      inv_mem' := fun {x} hx g Z hZ => by
        have := hx (g * x⁻¹) Z hZ
        rw [Units.val_mul, Matrix.mul_assoc (g.val), ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one] at this
        exact this.symm }
  have hKf : IsOpen (Kf : Set (GL (Fin a) k)) := Subgroup.isOpen_of_mem_nhds Kf (g := 1)
    (Filter.mem_of_superset hU fun x hx g Z hZ => hUf x hx g Z hZ)
  let K : Subgroup (GL (Fin a) k) := KO k (Fin a) ⊓ (detChar (Fin a) ν).ker ⊓ Kf
  have hK : IsOpen (K : Set (GL (Fin a) k)) := (isOpen_KO.inter hν.detChar).inter hKf
  have hKO : K ≤ KO k (Fin a) := le_trans inf_le_left inf_le_left
  have htw : ∀ x ∈ K, tw ν (a + b) x = 1 := fun x hx => by
    have h1 : ν (gdet x) = 1 := hx.1.2
    simp [tw, h1, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hx.1.1)]
  have hright : ∀ (g x : GL (Fin a) k) (Z : Matrix (Fin a) (Fin (a + b)) k), x ∈ K → Z ∈ slice k a (a + b) →
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := fun g x Z hx hZ => hx.2 g Z hZ
  obtain ⟨C, hC, hEC⟩ := GlobalTheory.T.continuous_slice_section_measure k a (a + b) Φ hΦ sec hsc hsl hun
  obtain ⟨R, hRd, hRc⟩ := GlobalTheory.T.compact_covered_by_open_cosets (GL (Fin a) k) K hK C hC
  set T : Set (Matrix (Fin a) (Fin (a + b)) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice k a (a + b), Y = x.val * Z} with hT
  have hrank : ∀ Y, Φ Y ≠ 0 → Y.rank = a := fun Y hY => by
    by_contra h; exact hY (hΦ.2 Y h)
  refine GlobalTheory.T.coinvariant_of_locally_constant_twist k ν β a b Φ (T.indicator 1) R hΦ.1
    (GlobalTheory.T.isLocallyConstant_indicator_mul_slice k a (a + b) K hK hKO (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b)) sec hsc hsl hun) (fun Y => ?_) (fun Y => ?_)
  · by_cases hY : Φ Y = 0
    · simp [hY]
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin a) k, (g⁻¹).val * Y ∈ slice k a (a + b) := ⟨sec Y, hsl Y (hrank Y hY)⟩
    set Z := (g⁻¹).val * Y with hZdef
    have hYZ : Y = g.val * Z := by rw [hZdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
    obtain ⟨r, hr, hrg⟩ := hRc g (hEC g Z hg (hYZ ▸ hY))
    rw [Finset.sum_eq_single r]
    · rw [Set.indicator_of_mem, Pi.one_apply, one_mul]
      exact ⟨r⁻¹ * g, hrg, Z, hg, by rw [hYZ, Units.val_mul, Matrix.mul_assoc]⟩
    · intro r' hr' hne
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨x', hx', Z', hZ', he⟩
      have h1 : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z ∈ slice k a (a + b) := by
        have : ((x'⁻¹ * r'⁻¹ * g : GL (Fin a) k)).val * Z = Z' := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [← hYZ, he, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [this]; exact hZ'
      have h2 := hun Z _ hg h1
      have h3 : g = r' * x' := by
        calc g = r' * x' * (x'⁻¹ * r'⁻¹ * g) := by group
          _ = r' * x' := by rw [h2, mul_one]
      exact hne (hRd r hr r' hr' (by
        have : r⁻¹ * r' = (r⁻¹ * g) * x'⁻¹ := by rw [h3]; group
        rw [this]; exact K.mul_mem hrg (K.inv_mem hx'))).symm
    · intro h; exact absurd hr h
  · by_cases hY : Y ∈ T
    · obtain ⟨x, hx, Z, hZ, rfl⟩ := hY
      rw [Set.indicator_of_mem (show x.val * Z ∈ T from ⟨x, hx, Z, hZ, rfl⟩), Pi.one_apply, one_mul]
      have e1 : ∀ r : GL (Fin a) k, Φ (r.val * (x.val * Z)) = Φ (r.val * Z) := fun r => by
        rw [← Matrix.mul_assoc]; exact hright r x Z hx hZ
      simp only [e1]
      have hZr : Z.rank = a := by
        obtain ⟨J, hJ, -⟩ := hZ
        exact (GlobalTheory.T.full_rank_iff_nonzero_minor k a (a + b) Z).2 ⟨J, by simp [minor, hJ]⟩
      have hint := GlobalTheory.T.haar_integral_over_coset_representatives k a K hK hKO (fun g => Φ (g.val * Z) * tw ν (a + b) g)
        (fun g x' hx' => by
          simp only [Units.val_mul, tw_mul, htw x' hx', mul_one]
          rw [hright g x' Z hx' hZ])
        R hRd (fun g hg => hRc g (hEC g Z hZ (left_ne_zero_of_mul hg)))
      rw [GlobalTheory.T.orbital_integral_vanishes_of_fibre k ν β a b Φ hfib Z hZr] at hint
      have hv := vol_ne_zero K hK hKO
      have := (mul_eq_zero.1 hint.symm).resolve_left (by exact_mod_cast hv)
      rw [← this]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    · simp [Set.indicator_of_notMem hY]
end GlobalTheory.RankFibreKer
