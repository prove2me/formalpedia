-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d7_dictInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/50af15d3-7bd6-5f22-90f3-437b8941fbf1

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty.AlgebraicCurve ModularCurve ModularCurve.CharPModel"

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord exists_unit_mul_zpow algebraMap_mem' toValuationSubring mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem (a : K) : algebraMap K F a ∈ w.toValuationSubring := w.algebraMap_mem' a

p2m_export "AlgebraicCurve.Place" "algebraMap_mem"

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using w.algebraMap_mem a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_nonunits_iff"

private theorem _root_.AlgebraicCurve.Place.mul_mem_nonunits {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

p2m_export "AlgebraicCurve.Place" "mul_mem_nonunits"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_pos {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_pos"

private theorem _root_.AlgebraicCurve.Place.mem_nonunits_iff_ord_pos {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.mem_of_ord_pos h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

p2m_export "AlgebraicCurve.Place" "mem_nonunits_iff_ord_pos"

private def _root_.AlgebraicCurve.Place.HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

p2m_export "AlgebraicCurve.Place" "HasValueAt"

private theorem _root_.AlgebraicCurve.Place.hasValueAt_algebraMap (a : K) : w.HasValueAt (algebraMap K F a) a := by
  simp [HasValueAt, ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "hasValueAt_algebraMap"

private theorem _root_.AlgebraicCurve.Place.mem_of_hasValueAt {f : F} {a : K} (h : w.HasValueAt f a) : f ∈ w.toValuationSubring := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (w.algebraMap_mem a)

p2m_export "AlgebraicCurve.Place" "mem_of_hasValueAt"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.unique {f : F} {a b : K} (ha : w.HasValueAt f a) (hb : w.HasValueAt f b) :
    a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((w.algebraMap_mem_nonunits_iff _).mp h)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.unique"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.add {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f + g) (a + b) := by
  have := add_mem hf hg
  rw [HasValueAt, map_add]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.add"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.neg {f : F} {a : K} (hf : w.HasValueAt f a) : w.HasValueAt (-f) (-a) := by
  have := neg_mem hf
  rw [HasValueAt, map_neg]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.neg"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.mul {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (w.mem_of_hasValueAt hg)
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hg (w.algebraMap_mem a)
  have := add_mem h1 h2
  rw [HasValueAt, map_mul]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.mul"
variable (A : ValuationSubring K)

private def _root_.AlgebraicCurve.Place.compSubring : Subring F where
  carrier := {f | ∃ a : A, w.HasValueAt f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simpa using ha.mul hb⟩
  one_mem' := ⟨1, by simpa using w.hasValueAt_algebraMap 1⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using w.hasValueAt_algebraMap 0⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, by simpa using ha.neg⟩

p2m_export "AlgebraicCurve.Place" "compSubring"

private def value : w.compSubring A →+* A where
  toFun f := Classical.choose f.2
  map_one' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).one_mem).unique (by
      simpa using w.hasValueAt_algebraMap 1)
  map_mul' f g := Subtype.ext <|
    (Classical.choose_spec (mul_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).mul (Classical.choose_spec g.2))
  map_zero' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).zero_mem).unique (by
      simpa using w.hasValueAt_algebraMap 0)
  map_add' f g := Subtype.ext <|
    (Classical.choose_spec (add_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).add (Classical.choose_spec g.2))

end Place
end AlgebraicCurve
set_option autoImplicit false
namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mul_mem one_mem nonunits_subset add_mem valuation_le_one_iff valuation"
p2m_open "ValuationSubring"
variable {K : Type*} [Field K] (A : ValuationSubring K)
section Quotient
open Polynomial
variable {F : Type*} [Field F] [Algebra K F]

private abbrev constants : A →+* F := (algebraMap K F).comp A.subtype

variable {A}

end Quotient
end ValuationSubring

open ModularCurve _root_.ModularCurve.CharPModel IsLocalRing in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (_hsq : Squarefree N) (_hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (_hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (_halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (_hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (_hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)
    (cc : fm.CuspChart) :
    ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by
  intro w τ ht hpole hres

  have hteq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
      / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N
      = jNBar N * ((jBar N)⁻¹) ^ N := by
    rw [div_eq_mul_inv, inv_pow]; rfl
  have ht' : jNBar N * ((jBar N)⁻¹) ^ N ∈ w.toValuationSubring := hteq ▸ ht
  have hres' : residue w.toValuationSubring ⟨jNBar N * ((jBar N)⁻¹) ^ N, ht'⟩
      = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) := by
    rw [← hres]; congr 1; exact Subtype.ext hteq.symm

  have hval : (jNBar N * ((jBar N)⁻¹) ^ N
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (τ : AlgebraicClosure ℚ))
      ∈ w.toValuationSubring.nonunits := by
    have e : algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ)
        = residue w.toValuationSubring
            (algebraMap (AlgebraicClosure ℚ) w.toValuationSubring (τ : AlgebraicClosure ℚ)) := rfl
    rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff] at hres'
    exact hres'

  have hmem := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole
      (⟨jNBar N * ((jBar N)⁻¹) ^ N, cc.tBar_mem⟩
        - ⟨constantsHom N A τ, fm.constInf_mem τ⟩)).mpr
    ⟨0, zero_mem (IsLocalRing.maximalIdeal A), by
      simpa [constantsHom, map_zero, sub_zero] using hval⟩
  have hpi : fm.piInf (⟨jNBar N * ((jBar N)⁻¹) ^ N, cc.tBar_mem⟩
        - ⟨constantsHom N A τ, fm.constInf_mem τ⟩)
      = (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)
          / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
        - algebraMap k (modularFunctionFieldC k N) (red τ) := by
    rw [map_sub, cc.piInf_t, fm.piInf_const, div_eq_mul_inv, inv_pow]
  rw [hpi] at hmem
  rcases eq_or_ne ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)
      / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
      - algebraMap k (modularFunctionFieldC k N) (red τ)) 0 with h0 | hne
  · exact Or.inl h0
  · exact Or.inr
      (((fm.spPlace hred dataAll hsep w).mem_nonunits_iff_ord_pos hne).mp hmem)

end

end S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty (solution)
