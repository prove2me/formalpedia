-- Prove2me | solution 1 for ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f34f37e4-ecd0-5f50-9e80-1ae8e40a84e3

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace SSTransportAux

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_jq (q : ℕ) [Fact q.Prime] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  have hqexp : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) =
      qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) := by
    ext m
    simp only [coeffEmb_coeff]
    by_cases h : (q : ℤ) ∣ m
    · obtain ⟨k, rfl⟩ := h
      rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
    · rw [qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]
  have key : ∀ (a b : ℕ) [NeZero a] [NeZero b], a = b → ∀ x : LaurentSeries (AlgebraicClosure ℚ),
      qExpand (AlgebraicClosure ℚ) a x = qExpand (AlgebraicClosure ℚ) b x := by
    intro a b _ _ h x; subst h; rfl
  rw [hqexp, coeffEmb_jq, jqNModC]
  exact (key (1 * q) q (one_mul q) _).symm

theorem not_mem_ssJSet_right {Ω : Type} [Field Ω] [DecidableEq Ω]
    (q : ℕ) [Fact q.Prime] [CharP Ω q] [PerfectField Ω] (a c : Ω)
    (h : (a ^ q - c) * (a - c ^ q) = 0) (ha : a ∉ ModularCurve.ssJSet q Ω) : c ∉ ModularCurve.ssJSet q Ω := by
  rcases mul_eq_zero.mp h with h | h
  · rw [sub_eq_zero] at h
    rw [← h, ModularCurve.pow_mem_ssJSet_iff]; exact ha
  · rw [sub_eq_zero] at h
    intro hc; apply ha
    rw [h]; exact (ModularCurve.pow_mem_ssJSet_iff q _).mpr hc

theorem not_mem_ssJSet_left {Ω : Type} [Field Ω] [DecidableEq Ω]
    (q : ℕ) [Fact q.Prime] [CharP Ω q] [PerfectField Ω] (a c : Ω)
    (h : (a ^ q - c) * (a - c ^ q) = 0) (hc : c ∉ ModularCurve.ssJSet q Ω) : a ∉ ModularCurve.ssJSet q Ω := by
  rcases mul_eq_zero.mp h with h | h
  · rw [sub_eq_zero] at h
    intro ha; apply hc; rw [← h]; exact (ModularCurve.pow_mem_ssJSet_iff q _).mpr ha
  · rw [sub_eq_zero] at h
    rw [h]; intro hh; exact hc ((ModularCurve.pow_mem_ssJSet_iff q _).mp hh)

theorem exists_sub_mul_sub_eq_natCast_mul {B : Type*} [CommRing B] (q : ℕ) [Fact q.Prime]
    (ι : B →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (jB j'B : B) (hιj : ι jB = jqModC (AlgebraicClosure ℚ))
    (hιj' : ι j'B = jqNModC (AlgebraicClosure ℚ) (1 * q)) :
    ∃ b₀ : B, (jB ^ q - j'B) * (jB - j'B ^ q) = (q : B) * b₀ := by
  have hjR : jqModC (AlgebraicClosure ℚ) ∈ ι.range := ⟨jB, hιj⟩
  have hj'R : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ ι.range := ⟨j'B, hιj'⟩
  have hK := ModularCurve.sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem q ι.range hjR hj'R
  rw [Ideal.mem_span_singleton] at hK
  obtain ⟨r, hr⟩ := hK
  obtain ⟨b₀, hb₀⟩ := r.2
  refine ⟨b₀, hι ?_⟩
  have h1 := congrArg Subtype.val hr
  simp only [Subring.coe_mul, Subring.coe_natCast, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub] at h1
  rw [map_mul ι (q : B) b₀, map_natCast, hb₀, ← h1]
  rw [map_mul, map_sub, map_sub, map_pow, map_pow, hιj, hιj']

theorem sub_mul_sub_apply_eq_zero {B : Type*} [CommRing B] {Ω : Type} [Field Ω] (q : ℕ) [CharP Ω q]
    (jB j'B b₀ : B) (hKB : (jB ^ q - j'B) * (jB - j'B ^ q) = (q : B) * b₀)
    (ψ : B →+* Ω) (c : Ω) (hψ : ψ j'B = c) :
    (ψ jB ^ q - c) * (ψ jB - c ^ q) = 0 := by
  have := congrArg ψ hKB
  rw [map_mul ψ (q : B), map_natCast, CharP.cast_eq_zero Ω q, zero_mul, map_mul, map_sub, map_sub, map_pow,
    map_pow, hψ] at this
  exact this

theorem ker_comp_eq {A E : Type*} [CommRing A] [Field E] [Algebra A E] {Ω : Type*} [Semiring Ω]
    (S : Subalgebra A E) (σ : E ≃ₐ[A] E) (σB : ↥S →+* ↥S) (hσB : ∀ b : ↥S, ((σB b : ↥S) : E) = σ (b : E))
    (y y' : Ideal ↥S)
    (htrans : ∀ (b : ↥S) (hb : σ.symm (b : E) ∈ S), b ∈ y' ↔ (⟨σ.symm (b : E), hb⟩ : ↥S) ∈ y)
    (φ' : ↥S →+* Ω) (hφ' : RingHom.ker φ' = y') :
    RingHom.ker (φ'.comp σB) = y := by
  ext b
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hφ']
  have hval : σ.symm ((σB b : ↥S) : E) = (b : E) := by rw [hσB]; exact σ.symm_apply_apply (b : E)
  have hb : σ.symm ((σB b : ↥S) : E) ∈ S := hval ▸ b.2
  have heq : (⟨σ.symm ((σB b : ↥S) : E), hb⟩ : ↥S) = b := Subtype.ext hval
  rw [htrans (σB b) hb, heq]

theorem core {A E : Type*} [CommRing A] [Field E] [Algebra A E]
    (q : ℕ) [Fact q.Prime] (S : Subalgebra A E)
    (ι : ↥S →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (jB j'B : ↥S) (hιj : ι jB = jqModC (AlgebraicClosure ℚ))
    (hιj' : ι j'B = jqNModC (AlgebraicClosure ℚ) (1 * q))
    (σ : E ≃ₐ[A] E) (hσS : ∀ b : E, b ∈ S ↔ σ b ∈ S) (hσj' : σ (j'B : E) = (j'B : E))
    (y y' : Ideal ↥S)
    (htrans : ∀ (b : ↥S) (hb : σ.symm (b : E) ∈ S), b ∈ y' ↔ (⟨σ.symm (b : E), hb⟩ : ↥S) ∈ y)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (hORD : ∀ φ : ↥S →+* Ω, RingHom.ker φ = y → φ jB ∉ ModularCurve.ssJSet q Ω)
    (φ' : ↥S →+* Ω) (hφ' : RingHom.ker φ' = y') : φ' jB ∉ ModularCurve.ssJSet q Ω := by
  haveI : PerfectField Ω := IsAlgClosed.perfectField Ω
  let σB : ↥S →ₐ[A] ↥S := (σ.toAlgHom.comp S.val).codRestrict S (fun b => (hσS b.1).mp b.2)
  have hσB : ∀ b : ↥S, (((σB : ↥S →+* ↥S) b : ↥S) : E) = σ (b : E) := fun _ => rfl
  have hker := ker_comp_eq S σ (σB : ↥S →+* ↥S) hσB y y' htrans φ' hφ'
  have hb_ss : (φ'.comp (σB : ↥S →+* ↥S)) jB ∉ ModularCurve.ssJSet q Ω := hORD _ hker
  obtain ⟨b₀, hKB⟩ := exists_sub_mul_sub_eq_natCast_mul q ι hι jB j'B hιj hιj'
  have hσj'B : (σB : ↥S →+* ↥S) j'B = j'B := Subtype.ext (by rw [hσB]; exact hσj')
  have h1 := sub_mul_sub_apply_eq_zero q jB j'B b₀ hKB φ' (φ' j'B) rfl
  have h2 := sub_mul_sub_apply_eq_zero q jB j'B b₀ hKB (φ'.comp (σB : ↥S →+* ↥S)) (φ' j'B)
    (by rw [RingHom.comp_apply, hσj'B])
  have hc := not_mem_ssJSet_right q _ _ h2 hb_ss
  exact not_mem_ssJSet_left q _ _ h1 hc

end SSTransportAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
      j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ →
    ∀ (σ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≃ₐ[↥A₁] ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      σ j' = j' →
      (∀ b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ↔ σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →

    ∀ (y y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)),
      (∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) (hb : σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
          b ∈ y'.asIdeal ↔ (⟨σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hb⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) ∈ y.asIdeal) →

      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω) →
      ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ' = y'.asIdeal →
          φ' (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hK1 hstabF hLD hRAT instA hconst j₁ hj₁ instF j' hj' hj'B σ hσj' hσB y y' htrans hORD Ω instΩ instΩp instΩc instΩd φ' hφ'

  let ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp
      ((algebraMap ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ↥(fieldBar q M')).comp (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
  have hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ι b = b.1.1.1 := fun _ => rfl
  have hι_inj : Function.Injective ι := by
    intro a b h
    rw [hι, hι] at h
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hιj : ι (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) = jqModC (AlgebraicClosure ℚ) := by
    rw [hι]
    change j₁.1.1 = _
    rw [show j₁.1 = _ from hj₁]
    exact SSTransportAux.coeffEmb_jq
  have hιj' : ι ⟨j', hj'B⟩ = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    rw [hι]
    change j'.1.1 = _
    rw [show j'.1.1 = _ from hj']
    exact SSTransportAux.coeffEmb_qExpand_jq q
  exact SSTransportAux.core q _ ι hι_inj _ ⟨j', hj'B⟩ hιj hιj' σ hσB hσj' _ _ htrans Ω (hORD Ω) φ' hφ'

end S_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_three (solution)
