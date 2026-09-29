-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/24c943be-e3b1-5036-824c-754837a183fc

import Mathlib
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top"
namespace CellMajorantLoc
p2m_open "HaarQuotient"

section Algebra

variable {G : Type*} [Group G] {H : Subgroup G}

theorem apply_out_mk {α : Type*} {f : G → α} (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (g : G) :
    f (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = f g := by
  have h : (MulAction.orbitRel H G) (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out g :=
    Quotient.exact (Quotient.out_eq _)
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.1 h
  rw [← hx]
  exact hfH x x.2 g

theorem apply_coe_mul {α : Type*} {f : G → α} (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g)
    (x : H) (g : G) : f ((x : G) * g) = f g :=
  hfH x x.2 g

end Algebra

section Measurability

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem measurable_weight [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · exact Measurable.tsum fun n =>
      (measurable_const.mul measurable_const).mul
        (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

theorem measurable_density [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

omit [TopologicalSpace G] in

theorem measurable_comp_out {α : Type*} [MeasurableSpace α] {H : Subgroup G} {f : G → α}
    (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => f q.out := by
  refine measurable_from_quotient.2 ?_
  have : (fun q : MulAction.orbitRel.Quotient H G => f q.out) ∘ Quotient.mk'' = f :=
    funext fun g => apply_out_mk hfH g
  rw [this]
  exact hf

end Measurability

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [BorelSpace G] in

theorem sFinite_of_isClosed (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] : SFinite μH := by
  haveI : SigmaCompactSpace H := hH.sigmaCompactSpace
  infer_instance

end Main

end HaarQuotient.CellMajorantLoc

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top"
namespace CellMajorantLoc
namespace LocalGL2Iwasawa
p2m_open "HaarQuotient"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 K) K v ⊤

def diagU (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) : G where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F), 0; 0, ((b⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagU (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ((diagU K v a b : G) : Mat) = !![(a : F), 0; 0, (b : F)] := rfl

theorem diagU_inv (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    (diagU K v a b)⁻¹ = diagU K v a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change ((diagU K v a b : G) : Mat) * ((diagU K v a⁻¹ b⁻¹ : G) : Mat) = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagU_mul (a b a' b' : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    diagU K v a b * diagU K v a' b' = diagU K v (a * a') (b * b') := by
  refine Units.ext ?_
  change ((diagU K v a b : G) : Mat) * ((diagU K v a' b' : G) : Mat) = ((diagU K v (a * a') (b * b') : G) : Mat)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section Setup

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem coe_unip_eq :
    ((unip K v : Subgroup G) : Set G) =
      {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip K v : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unip_comm (a b : (unip K v : Subgroup G)) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  change (a : G) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem coe_kzero_eq_localIntegralSet :
    ((kzero K v : Subgroup G) : Set G) = localIntegralSet K v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero K v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet K v

theorem isCompact_kzero : IsCompact ((kzero K v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet K v

theorem diagU_mem_kzero {a b : (HeightOneSpectrum.adicCompletion K v)ˣ}
    (ha : Valued.v (a : F) = 1) (hb : Valued.v (b : F) = 1) : diagU K v a b ∈ kzero K v := by
  have key : ∀ c d : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (c : F) = 1 → Valued.v (d : F) = 1 →
      ∀ i j, ((diagU K v c d : G) : Mat) i j ∈ (O) := by
    intro c d hc hd i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagU]
    fin_cases i <;> fin_cases j <;> simp [hc, hd]
  rw [mem_kzero_iff]
  refine ⟨key a b ha hb, ?_⟩
  rw [diagU_inv]
  refine key a⁻¹ b⁻¹ ?_ ?_
  · rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_one]

end Setup

section Uniformizer

theorem coe_uniformizer_ne_zero (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) : ((ϖ : O) : F) ≠ 0 := by
  intro h
  rw [h, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

def piUnit (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) : (HeightOneSpectrum.adicCompletion K v)ˣ :=
  Units.mk0 ((ϖ : O) : F) (coe_uniformizer_ne_zero K v ϖ hϖ)

theorem v_piUnit_zpow (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((piUnit K v ϖ hϖ) ^ k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  change Valued.v ((ϖ : O) : F) ^ k = _
  rw [hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

theorem exists_eq_piUnit_zpow_mul (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ∃ (m : ℤ) (w : (HeightOneSpectrum.adicCompletion K v)ˣ), Valued.v (w : F) = 1 ∧ u = piUnit K v ϖ hϖ ^ m * w := by
  have hu : Valued.v (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  set e : ℤ := WithZero.log (Valued.v (u : F)) with he
  refine ⟨-e, piUnit K v ϖ hϖ ^ e * u, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, v_piUnit_zpow, ← WithZero.exp_log hu, ← he, ← WithZero.exp_add,
      neg_add_cancel, WithZero.exp_zero]
  · rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

theorem piUnit_zpow_mem_integers_iff (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    (((piUnit K v ϖ hϖ) ^ k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) ∈ (O) ↔ 0 ≤ k := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, v_piUnit_zpow, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

def shellRep (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (mn : ℤ × ℤ) : G :=
  diagU K v (piUnit K v ϖ hϖ ^ mn.1) (piUnit K v ϖ hϖ ^ mn.2)

end Uniformizer

section Shells

theorem coe_unipotentGL2Hom (z : Multiplicative (HeightOneSpectrum.adicCompletion K v)) :
    ((unipotentGL2Hom z : G) : Mat) = !![1, z.toAdd; 0, 1] := rfl

theorem coe_diagU_inv_mul_unipotent_mul_diagU (a b a' b' : (HeightOneSpectrum.adicCompletion K v)ˣ)
    (z : Multiplicative (HeightOneSpectrum.adicCompletion K v)) :
    ((((diagU K v a b)⁻¹ * unipotentGL2Hom z * diagU K v a' b' : G)) : Mat) =
      !![((a⁻¹ * a' : (HeightOneSpectrum.adicCompletion K v)ˣ) : F), ((a⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * z.toAdd * b';
        0, ((b⁻¹ * b' : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)] := by
  rw [diagU_inv, Units.val_mul, Units.val_mul, coe_diagU, coe_diagU, coe_unipotentGL2Hom]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem shell_unique (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ))
    (mn mn' : ℤ × ℤ) (x : (unip K v : Subgroup G)) (k k' : (kzero K v : Subgroup G))
    (h : (x : G) * shellRep K v ϖ hϖ mn * k = shellRep K v ϖ hϖ mn' * k') : mn = mn' := by
  obtain ⟨z, hz⟩ := x.2
  set π := piUnit K v ϖ hϖ with hπ

  set M : G := (shellRep K v ϖ hϖ mn')⁻¹ * (x : G) * shellRep K v ϖ hϖ mn with hM
  have hMk : M = (k' : G) * (k : G)⁻¹ := by
    rw [hM, eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, ← mul_assoc (x : G), h, inv_mul_cancel_left]
  have hMmem : M ∈ kzero K v := by rw [hMk]; exact mul_mem k'.2 (inv_mem k.2)
  have hMinv : M⁻¹ ∈ kzero K v := inv_mem hMmem

  have hcoeM : (M : Mat) = !![((π ^ (mn.1 - mn'.1) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F),
      (((π ^ mn'.1)⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * z.toAdd * ((π ^ mn.2 : (HeightOneSpectrum.adicCompletion K v)ˣ) : F);
      0, ((π ^ (mn.2 - mn'.2) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)] := by
    rw [hM, ← hz, shellRep, shellRep, coe_diagU_inv_mul_unipotent_mul_diagU, ← zpow_neg, ← zpow_neg, ← zpow_add,
      ← zpow_add, neg_add_eq_sub, neg_add_eq_sub]
  have hcoeMinv : ((M⁻¹ : G) : Mat) = !![((π ^ (mn'.1 - mn.1) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F),
      (((π ^ mn.1)⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * (z⁻¹).toAdd * ((π ^ mn'.2 : (HeightOneSpectrum.adicCompletion K v)ˣ) : F);
      0, ((π ^ (mn'.2 - mn.2) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)] := by
    have : M⁻¹ = (shellRep K v ϖ hϖ mn)⁻¹ * unipotentGL2Hom z⁻¹ * shellRep K v ϖ hϖ mn' := by
      rw [hM, ← hz, map_inv]; group
    rw [this, shellRep, shellRep, coe_diagU_inv_mul_unipotent_mul_diagU, ← zpow_neg, ← zpow_neg, ← zpow_add,
      ← zpow_add, neg_add_eq_sub, neg_add_eq_sub]
  have i1 : 0 ≤ mn.1 - mn'.1 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v M).mp hMmem).1 0 0
    rwa [hcoeM] at this
  have i2 : 0 ≤ mn'.1 - mn.1 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v (M⁻¹)).mp hMinv).1 0 0
    rwa [hcoeMinv] at this
  have i3 : 0 ≤ mn.2 - mn'.2 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v M).mp hMmem).1 1 1
    rwa [hcoeM] at this
  have i4 : 0 ≤ mn'.2 - mn.2 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v (M⁻¹)).mp hMinv).1 1 1
    rwa [hcoeMinv] at this
  exact Prod.ext (by omega) (by omega)

end Shells

end HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient"

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top"
namespace CellMajorantLoc
namespace LocalGL2Iwasawa
p2m_open "HaarQuotient"

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def diagUHom : (HeightOneSpectrum.adicCompletion K v)ˣ × (HeightOneSpectrum.adicCompletion K v)ˣ →*
    GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) where
  toFun p := diagU K v p.1 p.2
  map_one' := by
    refine Units.ext ?_
    change ((diagU K v 1 1 : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) = 1
    rw [coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := (diagU_mul K v p.1 p.2 q.1 q.2).symm

theorem diagU_zpow (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) (n : ℤ) :
    (diagU K v a b) ^ n = diagU K v (a ^ n) (b ^ n) := by
  change (diagUHom K v (a, b)) ^ n = diagUHom K v ((a, b) ^ n)
  rw [map_zpow]

theorem scalarPi_eq_diagU (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) :
    scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ =
      diagU K v (piUnit K v ϖ hϖ) (piUnit K v ϖ hϖ) := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [scalarPi, piUnit]

theorem diagZ_eq_diagU (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) (d : ℤ) :
    diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ d = diagU K v (piUnit K v ϖ hϖ ^ d) 1 := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [diagZ, piUnit, Units.val_zpow_eq_zpow_val]

theorem scalarPi_zpow_mul_diagZ_eq_shellRep (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) (dn : ℤ × ℤ) :
    scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ ^ dn.2 *
        diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ dn.1 =
      shellRep K v ϖ hϖ (dn.2 + dn.1, dn.2) := by
  rw [scalarPi_eq_diagU K v ϖ hπ hϖ, diagZ_eq_diagU K v ϖ hπ hϖ, diagU_zpow, diagU_mul, shellRep, zpow_add, mul_one]

def shellEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun dn := (dn.2 + dn.1, dn.2)
  invFun mn := (mn.1 - mn.2, mn.2)
  left_inv dn := by ext <;> simp
  right_inv mn := by ext <;> simp

end HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"

namespace L3aAlpha

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.AdelicLevel HaarQuotient.CellMajorantLoc HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def varpiO : O :=
  ⟨(uniformizerUnit ℚ p : F), by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_uniformizerUnit, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    decide⟩

theorem varpiO_coe : ((varpiO p : O) : F) = (uniformizerUnit ℚ p : F) := rfl

theorem v_varpiO : Valued.v ((varpiO p : O) : F) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ p

theorem varpiO_ne_zero : algebraMap O F (varpiO p) ≠ 0 := (uniformizerUnit ℚ p).ne_zero

theorem piUnit_varpiO : piUnit ℚ p (varpiO p) (v_varpiO p) = uniformizerUnit ℚ p :=
  Units.ext rfl

def torus (dn : ℤ × ℤ) : G :=
  scalarPi (algebraMap O F (varpiO p)) (varpiO_ne_zero p) ^ dn.2 *
    diagZ (algebraMap O F (varpiO p)) (varpiO_ne_zero p) dn.1

theorem torus_eq_shellRep (dn : ℤ × ℤ) :
    torus p dn = shellRep ℚ p (varpiO p) (v_varpiO p) (shellEquiv dn) :=
  scalarPi_zpow_mul_diagZ_eq_shellRep ℚ p (varpiO p) (varpiO_ne_zero p) (v_varpiO p) dn

theorem diagZ_mul_scalarPi_zpow (d n : ℤ) :
    diagZ (algebraMap O F (varpiO p)) (varpiO_ne_zero p) d *
        scalarPi (algebraMap O F (varpiO p)) (varpiO_ne_zero p) ^ n = torus p (d, n) := by
  rw [torus, scalarPi_eq_diagU ℚ p (varpiO p) (varpiO_ne_zero p) (v_varpiO p),
    diagZ_eq_diagU ℚ p (varpiO p) (varpiO_ne_zero p) (v_varpiO p), diagU_zpow, diagU_mul, diagU_mul,
    mul_one, one_mul, mul_comm]

theorem diagUnits2_eq_diagU (a b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    (diagUnits2 a b : G) = diagU ℚ p a b :=
  Units.ext rfl

def cell (a : G) : Set G := {g : G | ∃ x ∈ unip ℚ p, ∃ k ∈ kzero ℚ p, g = x * a * k}

theorem cell_eq_iUnion (a : G) :
    cell p a = ⋃ x : (unip ℚ p : Subgroup G), (fun k : G => (x : G) * a * k) '' ((kzero ℚ p : Subgroup G) : Set G) := by
  ext g
  simp only [cell, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, k, hk, rfl⟩
    exact ⟨⟨x, hx⟩, k, hk, rfl⟩
  · rintro ⟨x, k, hk, rfl⟩
    exact ⟨x, x.2, k, hk, rfl⟩

theorem isOpen_cell (a : G) : IsOpen (cell p a) := by
  rw [cell_eq_iUnion]
  refine isOpen_iUnion fun x => ?_
  have : (fun k : G => (x : G) * a * k) = fun k => ((x : G) * a) * k := rfl
  rw [this]
  exact (isOpenMap_mul_left ((x : G) * a)) _ (isOpen_kzero ℚ p)

theorem mul_mem_cell_iff {a n : G} (hn : n ∈ unip ℚ p) (g : G) : n * g ∈ cell p a ↔ g ∈ cell p a := by
  constructor
  · rintro ⟨x, hx, k, hk, h⟩
    refine ⟨n⁻¹ * x, mul_mem (inv_mem hn) hx, k, hk, ?_⟩
    apply mul_left_cancel (a := n)
    rw [h]; group
  · rintro ⟨x, hx, k, hk, rfl⟩
    exact ⟨n * x, mul_mem hn hx, k, hk, by group⟩

theorem mem_cell_mul_iff {a k : G} (hk : k ∈ kzero ℚ p) (g : G) : g * k ∈ cell p a ↔ g ∈ cell p a := by
  constructor
  · rintro ⟨x, hx, k', hk', h⟩
    refine ⟨x, hx, k' * k⁻¹, mul_mem hk' (inv_mem hk), ?_⟩
    rw [← mul_assoc, ← h, mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨x, hx, k', hk', rfl⟩
    exact ⟨x, hx, k' * k, mul_mem hk' hk, by group⟩

theorem shellRep_mul_mem_cell_iff (mn mn' : ℤ × ℤ) {k : G} (hk : k ∈ kzero ℚ p) :
    shellRep ℚ p (varpiO p) (v_varpiO p) mn * k ∈ cell p (shellRep ℚ p (varpiO p) (v_varpiO p) mn') ↔
      mn = mn' := by
  constructor
  · rintro ⟨x, hx, k', hk', h⟩
    have h' : ((⟨x⁻¹, inv_mem hx⟩ : (unip ℚ p : Subgroup G)) : G) * shellRep ℚ p (varpiO p) (v_varpiO p) mn *
        ((⟨k, hk⟩ : (kzero ℚ p : Subgroup G)) : G) =
        shellRep ℚ p (varpiO p) (v_varpiO p) mn' * ((⟨k', hk'⟩ : (kzero ℚ p : Subgroup G)) : G) := by
      change x⁻¹ * shellRep ℚ p (varpiO p) (v_varpiO p) mn * k = shellRep ℚ p (varpiO p) (v_varpiO p) mn' * k'
      rw [mul_assoc, h, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact shell_unique ℚ p (varpiO p) (v_varpiO p) mn mn' _ _ _ h'
  · rintro rfl
    exact ⟨1, one_mem _, k, hk, by rw [one_mul]⟩

theorem torus_mul_mem_cell_iff (dn dn' : ℤ × ℤ) {k : G} (hk : k ∈ kzero ℚ p) :
    torus p dn * k ∈ cell p (torus p dn') ↔ dn = dn' := by
  rw [torus_eq_shellRep, torus_eq_shellRep, shellRep_mul_mem_cell_iff p _ _ hk]
  exact shellEquiv.injective.eq_iff

scoped instance : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

section UnitsMeas

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ p)]

theorem measurable_unitsVal : Measurable (Units.val : (HeightOneSpectrum.adicCompletion ℚ p)ˣ → F) :=
  comap_measurable Units.val

variable [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)]

scoped instance borelSpace_units : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := HeightOneSpectrum.adicCompletion ℚ p)]
    rfl⟩

scoped instance isHaarMeasure_units (μ : Measure F) [μ.IsAddHaarMeasure] :
    (Measure.comap Units.val (mulMeasure μ)).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p μ

end UnitsMeas
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p) := borelSpace_localBorel ℚ p
  set c : ℝ≥0 := (Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem absNorm_ne_zero : (Ideal.absNorm p.asIdeal : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot

theorem setLIntegral_kzero_mul_left [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [MeasurableMul G]
    {u : G} (hu : u ∈ kzero ℚ p) (h : G → ℝ≥0∞) :
    ∫⁻ k in ((kzero ℚ p : Subgroup G) : Set G), h (u * k) ∂μ = ∫⁻ k in ((kzero ℚ p : Subgroup G) : Set G), h k ∂μ := by
  have hK : MeasurableSet ((kzero ℚ p : Subgroup G) : Set G) := (isOpen_kzero ℚ p).measurableSet
  rw [← lintegral_indicator hK, ← lintegral_indicator hK]
  have : ((kzero ℚ p : Subgroup G) : Set G).indicator (fun k => h (u * k)) =
      fun k => ((kzero ℚ p : Subgroup G) : Set G).indicator h (u * k) := by
    funext k
    by_cases hk : k ∈ ((kzero ℚ p : Subgroup G) : Set G)
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (mul_mem hu hk)]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem]
      intro huk
      exact hk (by simpa using mul_mem (inv_mem hu) huk)
  rw [this, lintegral_mul_left_eq_self]

end L3aAlpha
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.L3aAlpha"

namespace L3aAlpha

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.AdelicLevel HaarQuotient.CellMajorantLoc HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def sl (dn : ℤ × ℤ) : Set (unip ℚ p : Subgroup G) :=
  {x | (torus p dn)⁻¹ * (x : G) * torus p dn ∈ kzero ℚ p}

def S (n : ℤ) : Set (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  {y | Valued.v (y : F) = WithZero.exp (-(n))}

set_option maxHeartbeats 4000000 in

theorem main :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI := localBorel ℚ p
    ∀ (μ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧
        ∀ f : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable f →
          (∀ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (n * g) = f g) →
          ∫⁻ g, f g ∂(μ.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN)) =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                f (diagUnits2 q.2.1 q.2.2 * q.1) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ENNReal)
                ∂((μ.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
              ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) := by
  intro μ _ μN _
  classical
  letI : MeasurableSpace G := localGLBorel ℚ p
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI : SecondCountableTopology G := secondCountableTopology_localGL ℚ p
  haveI : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI : μN.IsMulRightInvariant := ⟨fun g => by
    have : (fun h => h * g) = fun h => g * h := funext fun h => unip_comm ℚ p h g
    rw [this]
    exact map_mul_left_eq_self μN g⟩
  haveI : SFinite μN := sFinite_of_isClosed _ (isClosed_unip ℚ p) μN

  set K₀ : Set G := ((kzero ℚ p : Subgroup G) : Set G) with hK₀
  set μX : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))
    with hμX
  set D : G → ℝ≥0∞ := HaarQuotient.density (unip ℚ p : Subgroup G) μN with hD
  set ν : Measure G := μ.withDensity D with hν
  set qv : ℝ≥0∞ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ≥0∞) with hqv
  have hqv0 : qv ≠ 0 := by rw [hqv]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
  have hqvt : qv ≠ ⊤ := by rw [hqv]; exact ENNReal.natCast_ne_top _
  have hDm : Measurable D := measurable_density _ μN
  have hK₀m : MeasurableSet K₀ := (isOpen_kzero ℚ p).measurableSet
  have hμK0 : μ K₀ ≠ 0 := (isOpen_kzero ℚ p).measure_ne_zero μ ⟨1, one_mem _⟩
  have hμKt : μ K₀ ≠ ⊤ := (isCompact_kzero ℚ p).measure_lt_top.ne

  obtain ⟨hSm, hSu, hSmass, hSmod, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  set M₀ : ℝ≥0∞ := μX (S p 0) with hM₀
  have hshell : ∀ n : ℤ, μX (S p n) = M₀ := fun n => (hSmass n).1
  have hM₀0 : M₀ ≠ 0 := (hSmass 0).2.1.ne'
  have hM₀t : M₀ ≠ ⊤ := (hSmass 0).2.2.ne
  have hM₀2 : M₀ ^ 2 ≠ 0 := pow_ne_zero 2 hM₀0
  have hM₀2t : M₀ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hM₀t

  set Mc : ℝ≥0∞ := ν {g : G | ∃ n ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, g = n * k} with hMc
  have hpre : μN (((↑) : (unip ℚ p : Subgroup G) → G) ⁻¹' K₀) ≠ ⊤ :=
    ((isClosed_unip ℚ p).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_kzero ℚ p)).measure_lt_top.ne
  have hMc0 : Mc ≠ 0 ∧ Mc ≠ ⊤ := by
    have hset : {g : G | ∃ n ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, g = n * k} = ((unip ℚ p : Subgroup G) : Set G) * K₀ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, hK₀]
      constructor
      · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
      · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top μ
      (unip ℚ p : Subgroup G) (isClosed_unip ℚ p) μN (kzero ℚ p) (isOpen_kzero ℚ p) (isCompact_kzero ℚ p)
    have hopen : IsOpen (((unip ℚ p : Subgroup G) : Set G) * K₀) := (isOpen_kzero ℚ p).mul_left
    have hind : ∫⁻ g, (((unip ℚ p : Subgroup G) : Set G) * K₀).indicator (fun _ => (1 : ℝ≥0∞)) g ∂ν =
        ν (((unip ℚ p : Subgroup G) : Set G) * K₀) := lintegral_indicator_one hopen.measurableSet
    rw [hMc, hset, ← hind]
    exact ⟨by rw [h1]; exact (ENNReal.div_pos hμK0 hpre).ne', h2.ne⟩

  have hdec := AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2 ℚ p (varpiO p)
    (varpiO_ne_zero p) (v_varpiO p) μ μN
  have h9 := LanglandsTunnell.RankinSelberg.lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant p
    (varpiO_ne_zero p) (v_varpiO p) μ μN

  have hmass : ∀ dn : ℤ × ℤ, (μN (sl p dn))⁻¹ = Mc * qv ^ dn.1 / μ K₀ := by
    intro dn
    set f₀ : G → ℝ≥0∞ := (cell p (torus p dn)).indicator (fun _ => 1) with hf₀
    have hf₀m : Measurable f₀ := measurable_const.indicator (isOpen_cell p _).measurableSet
    have hf₀N : ∀ x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range, ∀ g : G,
        f₀ (x * g) = f₀ g := by
      intro x hx g
      by_cases hg : g ∈ cell p (torus p dn)
      · rw [hf₀, Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff p hx g).mpr hg)]
      · rw [hf₀, Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (mul_mem_cell_iff p hx g).mp hg)]
    have hf₀K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ g : G, f₀ (g * k) = f₀ g := by
      intro k hk g
      by_cases hg : g ∈ cell p (torus p dn)
      · rw [hf₀, Set.indicator_of_mem hg, Set.indicator_of_mem ((mem_cell_mul_iff p hk g).mpr hg)]
      · rw [hf₀, Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (mem_cell_mul_iff p hk g).mp hg)]
    obtain ⟨-, hsum⟩ := hdec f₀ hf₀m hf₀N
    have hsum' : ∫⁻ g, f₀ g * D g ∂μ =
        ∑' dn' : ℤ × ℤ, (μN (sl p dn'))⁻¹ * ∫⁻ k in K₀, f₀ (torus p dn' * k) ∂μ := hsum
    have hterm : ∀ dn' : ℤ × ℤ, ∫⁻ k in K₀, f₀ (torus p dn' * k) ∂μ = if dn' = dn then μ K₀ else 0 := by
      intro dn'
      rw [setLIntegral_congr_fun hK₀m (g := fun _ => if dn' = dn then 1 else 0) (fun k hk => ?_)]
      · rw [setLIntegral_const]
        split_ifs <;> simp
      · show f₀ (torus p dn' * k) = _
        rw [hf₀, Set.indicator_apply]
        simp only [torus_mul_mem_cell_iff p dn' dn hk]
    have hL : ∫⁻ g, f₀ g * D g ∂μ = (μN (sl p dn))⁻¹ * μ K₀ := by
      rw [hsum', tsum_eq_single dn]
      · rw [hterm, if_pos rfl]
      · intro dn' hne
        rw [hterm, if_neg hne, mul_zero]
    have h9' := h9 f₀ hf₀N hf₀K
    have h9'' : ∫⁻ g, f₀ g ∂ν =
        ∑' pp : ℤ × ℤ, Mc * qv ^ (pp.1 - pp.2) * f₀ (torus p (pp.1 - pp.2, pp.2)) := by
      rw [hν, hD, h9']
      refine tsum_congr fun pp => ?_
      rw [diagZ_mul_scalarPi_zpow]
    have hpt : ∀ pp : ℤ × ℤ, f₀ (torus p (pp.1 - pp.2, pp.2)) = if pp = shellEquiv dn then 1 else 0 := by
      intro pp
      have hmem : torus p (pp.1 - pp.2, pp.2) ∈ cell p (torus p dn) ↔ pp = shellEquiv dn := by
        rw [← mul_one (torus p (pp.1 - pp.2, pp.2)), torus_mul_mem_cell_iff p _ _ (one_mem _)]
        constructor
        · rintro rfl; simp [shellEquiv]
        · rintro rfl; simp [shellEquiv]
      rw [hf₀, Set.indicator_apply]
      simp only [hmem]
    have hR : ∫⁻ g, f₀ g ∂ν = Mc * qv ^ dn.1 := by
      rw [h9'', tsum_eq_single (shellEquiv dn)]
      · rw [hpt, if_pos rfl, mul_one]
        simp [shellEquiv]
      · intro pp hne
        rw [hpt, if_neg hne, mul_zero]
    have hB : ∫⁻ g, f₀ g ∂ν = ∫⁻ g, f₀ g * D g ∂μ := by
      rw [hν, lintegral_withDensity_eq_lintegral_mul μ hDm hf₀m]
      exact lintegral_congr fun g => mul_comm _ _
    have key : (μN (sl p dn))⁻¹ * μ K₀ = Mc * qv ^ dn.1 := by rw [← hL, ← hB, hR]
    rw [ENNReal.eq_div_iff hμK0 hμKt, mul_comm]
    exact key

  refine ⟨((Mc / μ K₀) / M₀ ^ 2).toReal, ?_, ?_⟩
  · refine ENNReal.toReal_pos ?_ ?_
    · exact (ENNReal.div_pos (ENNReal.div_pos hMc0.1 hμKt).ne' hM₀2t).ne'
    · exact ENNReal.div_ne_top (ENNReal.div_ne_top hMc0.2 hμK0) hM₀2
  intro f hf hfN
  set I : ℤ × ℤ → ℝ≥0∞ := fun ij => ∫⁻ k in K₀, f (shellRep ℚ p (varpiO p) (v_varpiO p) ij * k) ∂μ with hI
  set Ssum : ℝ≥0∞ := ∑' ij : ℤ × ℤ, qv ^ (ij.1 - ij.2) * I ij with hSsum

  have hLHS : ∫⁻ g, f g ∂ν = (Mc / μ K₀) * Ssum := by
    obtain ⟨-, hsum⟩ := hdec f hf hfN
    have hsum' : ∫⁻ g, f g * D g ∂μ =
        ∑' dn : ℤ × ℤ, (μN (sl p dn))⁻¹ * ∫⁻ k in K₀, f (torus p dn * k) ∂μ := hsum
    rw [hν, lintegral_withDensity_eq_lintegral_mul μ hDm hf,
      show (∫⁻ g, (D * f) g ∂μ) = ∫⁻ g, f g * D g ∂μ from lintegral_congr fun g => mul_comm _ _, hsum']
    have hre : ∀ dn : ℤ × ℤ, (μN (sl p dn))⁻¹ * ∫⁻ k in K₀, f (torus p dn * k) ∂μ =
        (fun ij : ℤ × ℤ => (Mc / μ K₀) * (qv ^ (ij.1 - ij.2) * I ij)) (shellEquiv dn) := by
      intro dn
      rw [hmass dn, torus_eq_shellRep]
      simp only [shellEquiv, Equiv.coe_fn_mk, add_sub_cancel_left, hI]
      simp only [div_eq_mul_inv]
      ring
    rw [tsum_congr hre, Equiv.tsum_eq shellEquiv (fun ij : ℤ × ℤ => (Mc / μ K₀) * (qv ^ (ij.1 - ij.2) * I ij)),
      ENNReal.tsum_mul_left]

  have hψ : Measurable (fun qq : G × ((HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ) =>
      diagUnits2 qq.2.1 qq.2.2 * qq.1) := by
    apply Continuous.measurable
    refine Continuous.mul ?_ continuous_fst
    have hc : Continuous (fun ab : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        (diagUnits2 ab.1 ab.2 : G)) := by
      rw [Units.continuous_iff]
      constructor
      · refine continuous_matrix fun i j => ?_
        fin_cases i <;> fin_cases j
        · simp [diagUnits2]
          exact Units.continuous_val.comp continuous_fst
        · simpa [diagUnits2] using continuous_const
        · simpa [diagUnits2] using continuous_const
        · simp [diagUnits2]
          exact Units.continuous_val.comp continuous_snd
      · refine continuous_matrix fun i j => ?_
        fin_cases i <;> fin_cases j
        · simp [diagUnits2]
          exact (Units.continuous_coe_inv.comp continuous_fst : Continuous fun a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((a.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)).congr
            fun a => Units.val_inv_eq_inv_val _
        · simpa [diagUnits2] using continuous_const
        · simpa [diagUnits2] using continuous_const
        · simp [diagUnits2]
          exact (Units.continuous_coe_inv.comp continuous_snd : Continuous fun a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((a.2⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)).congr
            fun a => Units.val_inv_eq_inv_val _
    exact hc.comp continuous_snd
  have hmodm : Measurable (fun qq : G × ((HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ) =>
      (modulus ((qq.2.2 * qq.2.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞)) := by
    have : (fun qq : G × ((HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ) =>
        (modulus ((qq.2.2 * qq.2.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞)) =
        fun qq => ((‖((qq.2.2 * qq.2.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖₊ : ℝ≥0∞)) := by
      funext qq
      rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
    rw [this]
    refine Measurable.coe_nnreal_ennreal (Continuous.measurable ?_)
    exact continuous_nnnorm.comp (Units.continuous_val.comp
      ((continuous_snd.comp continuous_snd).mul (continuous_fst.comp continuous_snd).inv))
  have hΨm : Measurable (fun qq : G × ((HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ) =>
      f (diagUnits2 qq.2.1 qq.2.2 * qq.1) *
        (modulus ((qq.2.2 * qq.2.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞)) :=
    (hf.comp hψ).mul hmodm
  rw [lintegral_prod_symm _ hΨm.aemeasurable]
  have hinner : ∀ (ij : ℤ × ℤ) (ab : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ),
      ab ∈ S p ij.1 ×ˢ S p ij.2 →
      ∫⁻ k, f (diagUnits2 ab.1 ab.2 * k) * (modulus ((ab.2 * ab.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞)
        ∂(μ.restrict K₀) = qv ^ (ij.1 - ij.2) * I ij := by
    rintro ⟨i, j⟩ ⟨a, b⟩ ⟨ha, hb⟩
    simp only [S, Set.mem_setOf_eq] at ha hb
    dsimp only
    rw [lintegral_mul_const _ (show Measurable (fun k : G => f (diagUnits2 a b * k)) from hf.comp (measurable_const_mul _))]

    have hmem : b * a⁻¹ ∈ {y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ | Valued.v (y : F) = WithZero.exp (-(j - i))} := by
      simp only [Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, ha, hb,
        ← WithZero.exp_neg, ← WithZero.exp_add]
      congr 1
      ring
    have hmodR := hSmod (j - i) (b * a⁻¹) hmem
    have hmodE : (modulus ((b * a⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞) = qv ^ (i - j) := by
      have h1 : modulus ((b * a⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) =
          ((Ideal.absNorm p.asIdeal : ℕ) : ℝ≥0) ^ (i - j) := by
        apply NNReal.coe_injective
        rw [NNReal.coe_zpow, NNReal.coe_natCast, hmodR, neg_sub]
      have hq' : ((Ideal.absNorm p.asIdeal : ℕ) : ℝ≥0) ≠ 0 := by
        exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
      rw [h1, ENNReal.coe_zpow hq', ENNReal.coe_natCast]

    have hw₁ : Valued.v ((((piUnit ℚ p (varpiO p) (v_varpiO p) ^ i)⁻¹ * a :
        (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) = 1 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, v_piUnit_zpow, ha, ← WithZero.exp_neg,
        ← WithZero.exp_add, neg_neg, add_neg_cancel, WithZero.exp_zero]
    have hw₂ : Valued.v ((((piUnit ℚ p (varpiO p) (v_varpiO p) ^ j)⁻¹ * b :
        (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) = 1 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, v_piUnit_zpow, hb, ← WithZero.exp_neg,
        ← WithZero.exp_add, neg_neg, add_neg_cancel, WithZero.exp_zero]
    have hdiag : (diagUnits2 a b : G) = shellRep ℚ p (varpiO p) (v_varpiO p) (i, j) *
        diagU ℚ p ((piUnit ℚ p (varpiO p) (v_varpiO p) ^ i)⁻¹ * a) ((piUnit ℚ p (varpiO p) (v_varpiO p) ^ j)⁻¹ * b) := by
      rw [diagUnits2_eq_diagU, shellRep, diagU_mul, mul_inv_cancel_left, mul_inv_cancel_left]
    have hKinv : ∫⁻ k in K₀, f (diagUnits2 a b * k) ∂μ = I (i, j) := by
      simp only [hI, hdiag, mul_assoc]
      exact setLIntegral_kzero_mul_left p μ (diagU_mem_kzero ℚ p hw₁ hw₂) (fun k => f (shellRep ℚ p (varpiO p) (v_varpiO p) (i, j) * k))
    rw [hKinv, hmodE, mul_comm]
  have hSmeas2 : ∀ ij : ℤ × ℤ, MeasurableSet (S p ij.1 ×ˢ S p ij.2) := fun ij => (hSm _).prod (hSm _)
  have hdisj : Pairwise (Function.onFun Disjoint fun ij : ℤ × ℤ => S p ij.1 ×ˢ S p ij.2) := by
    intro ij ij' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨ha', hb'⟩
    exact hne (Prod.ext ((hSu a).unique ha ha') ((hSu b).unique hb hb'))
  have hcover : (⋃ ij : ℤ × ℤ, S p ij.1 ×ˢ S p ij.2) = Set.univ := by
    ext ab
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, iff_true]
    obtain ⟨i, hi, -⟩ := hSu ab.1
    obtain ⟨j, hj, -⟩ := hSu ab.2
    exact ⟨(i, j), hi, hj⟩
  have hRHS : ∫⁻ ab, ∫⁻ k, f (diagUnits2 ab.1 ab.2 * k) *
        (modulus ((ab.2 * ab.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞) ∂(μ.restrict K₀) ∂(μX.prod μX) =
      M₀ ^ 2 * Ssum := by
    calc ∫⁻ ab, ∫⁻ k, f (diagUnits2 ab.1 ab.2 * k) *
          (modulus ((ab.2 * ab.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞) ∂(μ.restrict K₀) ∂(μX.prod μX)
        = ∫⁻ ab, ∫⁻ k, f (diagUnits2 ab.1 ab.2 * k) *
          (modulus ((ab.2 * ab.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞) ∂(μ.restrict K₀)
            ∂((μX.prod μX).restrict (⋃ ij : ℤ × ℤ, S p ij.1 ×ˢ S p ij.2)) := by rw [hcover, Measure.restrict_univ]
      _ = ∑' ij : ℤ × ℤ, ∫⁻ ab in S p ij.1 ×ˢ S p ij.2, ∫⁻ k, f (diagUnits2 ab.1 ab.2 * k) *
          (modulus ((ab.2 * ab.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0∞) ∂(μ.restrict K₀)
            ∂(μX.prod μX) := by rw [Measure.restrict_iUnion hdisj hSmeas2, lintegral_sum_measure]
      _ = ∑' ij : ℤ × ℤ, ∫⁻ ab in S p ij.1 ×ˢ S p ij.2, qv ^ (ij.1 - ij.2) * I ij ∂(μX.prod μX) :=
          tsum_congr fun ij => setLIntegral_congr_fun (hSmeas2 ij) (fun ab hab => hinner ij ab hab)
      _ = ∑' ij : ℤ × ℤ, qv ^ (ij.1 - ij.2) * I ij * M₀ ^ 2 := by
          refine tsum_congr fun ij => ?_
          rw [setLIntegral_const, Measure.prod_prod, hshell, hshell, sq]
      _ = M₀ ^ 2 * Ssum := by rw [ENNReal.tsum_mul_right, mul_comm]
  rw [hLHS, hRHS, ENNReal.ofReal_toReal (ENNReal.div_ne_top (ENNReal.div_ne_top hMc0.2 hμK0) hM₀2), ← mul_assoc,
    ENNReal.div_mul_cancel hM₀2 hM₀2t]

end L3aAlpha
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2.L3aAlpha"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧
        ∀ f : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable f →
          (∀ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (n * g) = f g) →
          ∫⁻ g, f g ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                f (diagUnits2 q.2.1 q.2.2 * q.1) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
              ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) :=
  L3aAlpha.main p

end
end S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_withDensity_density_eq_mul_lintegral_prod_diagUnits2 (solution)
