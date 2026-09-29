-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.piInf_range_localizes_of_not_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d2d656bd-b810-5af1-85a2-17a8e2167a50

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_red_surjective
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_piInf_range_localizes_of_not_affine
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
open AlgebraicCurve ModularCurve ModularCurve.CharPModel Polynomial
namespace JacJ9ChartB1

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

private theorem affineBaseFin_le (fm : FibreModel N A ℓ k red) : affineBaseFin N A ≤ fm.BFin := by
  refine Subring.closure_le.mpr ?_
  rintro y (⟨a, rfl⟩ | hy)
  · exact fm.constFin_mem a
  · rw [Set.mem_singleton_iff] at hy
    exact hy ▸ fm.jBar_mem

private theorem piFin_affineBaseFin_mem (fm : FibreModel N A ℓ k red)
    (T : Subring (modularFunctionFieldC k N))
    (hconst : ∀ a : A, algebraMap k (modularFunctionFieldC k N) (red a) ∈ T)
    (hj : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ T)
    (c : affineBaseFin N A) :
    fm.piFin (Subring.inclusion (affineBaseFin_le fm) c) ∈ T := by

  have hgen : Set.range (constantsHom N A) ∪ {jBar N} ⊆
      (((T.comap fm.piFin).map fm.BFin.subtype : Subring _) : Set _) := by
    rintro y (⟨a, rfl⟩ | hy)
    · refine Subring.mem_map.mpr ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, ?_, rfl⟩
      rw [Subring.mem_comap, fm.piFin_const]
      exact hconst a
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine Subring.mem_map.mpr ⟨⟨jBar N, fm.jBar_mem⟩, ?_, rfl⟩
      rw [Subring.mem_comap, fm.piFin_j]
      exact hj
  have hc : (c : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈
      ((T.comap fm.piFin).map fm.BFin.subtype : Subring _) :=
    Subring.closure_le.mpr hgen c.2
  obtain ⟨b', hb', hb'c⟩ := Subring.mem_map.mp hc
  have hbc : b' = Subring.inclusion (affineBaseFin_le fm) c := Subtype.ext hb'c
  rw [← hbc]
  exact Subring.mem_comap.mp hb'

private theorem _root_.JacJ9ChartB1.exists_monic_coeff_mem (fm : FibreModel N A ℓ k red)
    (T : Subring (modularFunctionFieldC k N))
    (hconst : ∀ a : A, algebraMap k (modularFunctionFieldC k N) (red a) ∈ T)
    (hj : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ T) (b : fm.BFin) :
    ∃ P : Polynomial (modularFunctionFieldC k N),
      P.Monic ∧ (∀ i, P.coeff i ∈ T) ∧ P.eval (fm.piFin b) = 0 := by
  obtain ⟨p, hp, hpb⟩ := fm.integralFin b

  set ψ : affineBaseFin N A →+* modularFunctionFieldC k N :=
    fm.piFin.comp (Subring.inclusion (affineBaseFin_le fm)) with hψ

  have hroot : p.eval₂ (Subring.inclusion (affineBaseFin_le fm)) b = 0 := by
    have h := Polynomial.hom_eval₂ p (Subring.inclusion (affineBaseFin_le fm)) fm.BFin.subtype b
    have hcomp : fm.BFin.subtype.comp (Subring.inclusion (affineBaseFin_le fm)) =
        (affineBaseFin N A).subtype := RingHom.ext fun _ => rfl
    rw [hcomp] at h
    have h0 : fm.BFin.subtype (p.eval₂ (Subring.inclusion (affineBaseFin_le fm)) b) = 0 :=
      h.trans hpb
    exact (map_eq_zero_iff _ Subtype.val_injective).mp h0
  refine ⟨p.map ψ, hp.map ψ, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact piFin_affineBaseFin_mem fm T hconst hj (p.coeff i)
  · rw [Polynomial.eval_map, hψ, ← Polynomial.hom_eval₂, hroot, map_zero]

p2m_export "JacJ9ChartB1" "exists_monic_coeff_mem"

private theorem piFin_mem_of_jqModC_mem
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (fm : FibreModel N A ℓ k red)
    (v : Place k (modularFunctionFieldC k N))
    (hv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring)
    (b : fm.BFin) : fm.piFin b ∈ v.toValuationSubring := by
  obtain ⟨P, hP, hcoeff, heval⟩ :=
    exists_monic_coeff_mem fm v.toValuationSubring.toSubring (fun a => v.algebraMap_mem' (red a))
      hv b
  exact v.mem_of_eval_monic_eq_zero hP hcoeff heval

end JacJ9ChartB1

namespace JacJ9ChartB1Inf

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

private theorem affineBaseInf_le (fm : FibreModel N A ℓ k red) : affineBaseInf N A ≤ fm.BInf := by
  refine Subring.closure_le.mpr ?_
  rintro y (⟨a, rfl⟩ | hy)
  · exact fm.constInf_mem a
  · rw [Set.mem_singleton_iff] at hy
    exact hy ▸ fm.jInvBar_mem

private theorem piInf_affineBaseInf_mem (fm : FibreModel N A ℓ k red)
    (T : Subring (modularFunctionFieldC k N))
    (hconst : ∀ a : A, algebraMap k (modularFunctionFieldC k N) (red a) ∈ T)
    (hjinv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ ∈ T)
    (c : affineBaseInf N A) :
    fm.piInf (Subring.inclusion (affineBaseInf_le fm) c) ∈ T := by
  have hgen : Set.range (constantsHom N A) ∪ {(jBar N)⁻¹} ⊆
      (((T.comap fm.piInf).map fm.BInf.subtype : Subring _) : Set _) := by
    rintro y (⟨a, rfl⟩ | hy)
    · refine Subring.mem_map.mpr ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, ?_, rfl⟩
      rw [Subring.mem_comap, fm.piInf_const]
      exact hconst a
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine Subring.mem_map.mpr ⟨⟨(jBar N)⁻¹, fm.jInvBar_mem⟩, ?_, rfl⟩
      rw [Subring.mem_comap, fm.piInf_jInv]
      exact hjinv
  have hc : (c : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈
      ((T.comap fm.piInf).map fm.BInf.subtype : Subring _) :=
    Subring.closure_le.mpr hgen c.2
  obtain ⟨b', hb', hb'c⟩ := Subring.mem_map.mp hc
  have hbc : b' = Subring.inclusion (affineBaseInf_le fm) c := Subtype.ext hb'c
  rw [← hbc]
  exact Subring.mem_comap.mp hb'

private theorem _root_.JacJ9ChartB1Inf.exists_monic_coeff_mem (fm : FibreModel N A ℓ k red)
    (T : Subring (modularFunctionFieldC k N))
    (hconst : ∀ a : A, algebraMap k (modularFunctionFieldC k N) (red a) ∈ T)
    (hjinv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ ∈ T) (b : fm.BInf) :
    ∃ P : Polynomial (modularFunctionFieldC k N),
      P.Monic ∧ (∀ i, P.coeff i ∈ T) ∧ P.eval (fm.piInf b) = 0 := by
  obtain ⟨p, hp, hpb⟩ := fm.integralInf b
  set ψ : affineBaseInf N A →+* modularFunctionFieldC k N :=
    fm.piInf.comp (Subring.inclusion (affineBaseInf_le fm)) with hψ
  have hroot : p.eval₂ (Subring.inclusion (affineBaseInf_le fm)) b = 0 := by
    have h := Polynomial.hom_eval₂ p (Subring.inclusion (affineBaseInf_le fm)) fm.BInf.subtype b
    have hcomp : fm.BInf.subtype.comp (Subring.inclusion (affineBaseInf_le fm)) =
        (affineBaseInf N A).subtype := RingHom.ext fun _ => rfl
    rw [hcomp] at h
    have h0 : fm.BInf.subtype (p.eval₂ (Subring.inclusion (affineBaseInf_le fm)) b) = 0 :=
      h.trans hpb
    exact (map_eq_zero_iff _ Subtype.val_injective).mp h0
  refine ⟨p.map ψ, hp.map ψ, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact piInf_affineBaseInf_mem fm T hconst hjinv (p.coeff i)
  · rw [Polynomial.eval_map, hψ, ← Polynomial.hom_eval₂, hroot, map_zero]

p2m_export "JacJ9ChartB1Inf" "exists_monic_coeff_mem"
end JacJ9ChartB1Inf

namespace JacJ9ChartB2

variable (k : Type*) [Field k] (N : ℕ) [NeZero N]

private noncomputable abbrev jC : modularFunctionFieldC k N := ⟨jqModC k, jqModC_mem k N⟩

private noncomputable abbrev E : IntermediateField k (LaurentSeries k) := IntermediateField.adjoin k {jqModC k}

private noncomputable abbrev E' : IntermediateField k (modularFunctionFieldC k N) := IntermediateField.adjoin k {jC k N}

private noncomputable abbrev EN : IntermediateField (E k) (LaurentSeries k) := IntermediateField.adjoin (E k) {jqNModC k N}

private theorem mem_EN_iff (x : LaurentSeries k) : x ∈ EN k N ↔ x ∈ modularFunctionFieldC k N := by
  have h : (EN k N).restrictScalars k = modularFunctionFieldC k N :=
    IntermediateField.adjoin_simple_adjoin_simple (F := k) (α := jqModC k) (jqNModC k N)
  rw [← IntermediateField.mem_restrictScalars k, h]

private theorem mem_E'_iff (y : modularFunctionFieldC k N) : y ∈ E' k N ↔ (y : LaurentSeries k) ∈ E k := by
  have h : IntermediateField.lift (E' k N) = E k := IntermediateField.lift_adjoin_simple (F := k) (modularFunctionFieldC k N) (jC k N)
  exact (IntermediateField.mem_lift (E := E' k N) y).symm.trans (by rw [h])

private theorem E_le_C (x : LaurentSeries k) (hx : x ∈ E k) : x ∈ modularFunctionFieldC k N :=
  (mem_EN_iff k N x).mp (IntermediateField.algebraMap_mem (EN k N) (⟨x, hx⟩ : E k))

private noncomputable def e₁ : E k ≃+* E' k N where
  toFun x := ⟨⟨x.1, E_le_C k N x.1 x.2⟩, (mem_E'_iff k N _).mpr x.2⟩
  invFun y := ⟨(y.1 : LaurentSeries k), (mem_E'_iff k N y.1).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def e₂ : EN k N ≃+* modularFunctionFieldC k N where
  toFun x := ⟨x.1, (mem_EN_iff k N x.1).mp x.2⟩
  invFun y := ⟨y.1, (mem_EN_iff k N y.1).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem he :
    RingHom.comp (algebraMap (E' k N) (modularFunctionFieldC k N)) (e₁ k N : E k →+* E' k N) =
      RingHom.comp (e₂ k N : EN k N →+* modularFunctionFieldC k N) (algebraMap (E k) (EN k N)) :=
  RingHom.ext fun _ => rfl

variable {k N} in
private theorem isSeparable_jqNModC_E (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N) :
    IsSeparable (E k) (jqNModC k N) :=
  ModularCurve.isSeparable_jqNModC_of_good k N ℓ hℓN

private theorem finiteDimensional_and_isSeparable_adjoin_jC
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N) :
    FiniteDimensional (IntermediateField.adjoin k ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
        (modularFunctionFieldC k N) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
        (modularFunctionFieldC k N) := by
  have hsep : IsSeparable (E k) (jqNModC k N) := isSeparable_jqNModC_E ℓ hℓN
  haveI hfin : FiniteDimensional (E k) (EN k N) := IntermediateField.adjoin.finiteDimensional hsep.isIntegral
  haveI hsepEN : Algebra.IsSeparable (E k) (EN k N) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (E k) (LaurentSeries k)).mpr hsep
  exact ⟨Module.Finite.of_equiv_equiv (e₁ k N) (e₂ k N) (he k N),
    Algebra.IsSeparable.of_equiv_equiv (e₁ k N) (e₂ k N) (he k N)⟩

end JacJ9ChartB2

namespace JacJ9ChartInf

open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel

private noncomputable abbrev jt (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    modularFunctionFieldC k N :=
  ⟨jqModC k, jqModC_mem k N⟩

variable {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

variable (k N) in

private theorem adjoin_inv_eq :
    IntermediateField.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)) =
      IntermediateField.adjoin k ({jt k N} : Set (modularFunctionFieldC k N)) := by
  refine le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr ?_)
    (IntermediateField.adjoin_simple_le_iff.mpr ?_)
  · exact inv_mem (IntermediateField.mem_adjoin_simple_self k (jt k N))
  · have h := inv_mem (IntermediateField.mem_adjoin_simple_self k (jt k N)⁻¹)
    rwa [inv_inv] at h

private theorem mem_chartRing_iff_exists (fm : FibreModel N A ℓ k red)
    (x : modularFunctionFieldC k N) :
    x ∈ CurveModel.chartRing k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)) ↔
      ∃ b : fm.BInf, fm.piInf b = x := by
  constructor
  · intro hx
    have hint : IsIntegral (Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N))) x :=
      (CurveModel.mem_chartRing_iff k).mp hx

    have hle : ∀ y : modularFunctionFieldC k N,
        y ∈ Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)) →
          y ∈ fm.piInf.range := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨⟨(jBar N)⁻¹, fm.jInvBar_mem⟩, fm.piInf_jInv⟩
      | algebraMap c =>
        obtain ⟨a, rfl⟩ := FibreModel.red_surjective N A ℓ k red fm c
        exact ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, fm.piInf_const a⟩
      | add y z _ _ hy hz => exact add_mem hy hz
      | mul y z _ _ hy hz => exact mul_mem hy hz
    obtain ⟨p, hp, hpx⟩ := hint
    set φ : Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)) →+* fm.piInf.range :=
      (algebraMap (Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
          (modularFunctionFieldC k N)).codRestrict fm.piInf.range (fun y => hle y y.2) with hφ
    have hcomp : fm.piInf.range.subtype.comp φ =
        algebraMap (Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
          (modularFunctionFieldC k N) :=
      RingHom.ext fun _ => rfl
    refine fm.intClosed_piInf x ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hpx
  · rintro ⟨b, rfl⟩
    obtain ⟨P, hP, hcoeff, heval⟩ := JacJ9ChartB1Inf.exists_monic_coeff_mem fm
      (Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N))).toSubring
      (fun a => Subalgebra.algebraMap_mem _ (red a)) (Algebra.self_mem_adjoin_singleton k _) b
    rw [CurveModel.mem_chartRing_iff]
    have hlift : P ∈ Polynomial.lifts (algebraMap
        (Algebra.adjoin k ({(jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
        (modularFunctionFieldC k N)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨P.coeff n, hcoeff n⟩, rfl⟩
    obtain ⟨Q, hQmap, -, hQmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP
    refine ⟨Q, hQmonic, ?_⟩
    rw [← Polynomial.eval_map, hQmap, heval]

end JacJ9ChartInf

open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel in
theorem solution
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k) (fm : FibreModel N A ℓ k red)
    (v : Place k (modularFunctionFieldC k N))
    (hv : ¬ ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring ∧
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring)) :
    (∀ b : fm.BInf, fm.piInf b ∈ v.toValuationSubring) ∧
      ∀ g : modularFunctionFieldC k N, g ∈ v.toValuationSubring →
        ∃ b b' : fm.BInf, ¬ v.HasValue (fm.piInf b') (0 : k) ∧ g * fm.piInf b' = fm.piInf b := by

  have hjN : JacJ9ChartInf.jt k N ∈ v.toValuationSubring →
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring := by
    intro hj
    obtain ⟨P, hP, hcoeff, heval⟩ := JacJ9ChartB1.exists_monic_coeff_mem fm
      v.toValuationSubring.toSubring (fun a => v.algebraMap_mem' (red a)) hj ⟨jNBar N, fm.jNBar_mem⟩
    rw [fm.piFin_jN] at heval
    exact v.mem_of_eval_monic_eq_zero hP hcoeff heval
  have hjt : JacJ9ChartInf.jt k N ∉ v.toValuationSubring := fun hj => hv ⟨hj, hjN hj⟩
  have hjinv : (JacJ9ChartInf.jt k N)⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem _).resolve_left hjt
  refine ⟨fun b => ?_, fun g hg => ?_⟩
  · obtain ⟨P, hP, hcoeff, heval⟩ := JacJ9ChartB1Inf.exists_monic_coeff_mem fm
      v.toValuationSubring.toSubring (fun a => v.algebraMap_mem' (red a)) hjinv b
    exact v.mem_of_eval_monic_eq_zero hP hcoeff heval

  obtain ⟨hfd, hsep⟩ := JacJ9ChartB2.finiteDimensional_and_isSeparable_adjoin_jC k N ℓ hℓN
  haveI : FiniteDimensional
      (IntermediateField.adjoin k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := by
    rw [JacJ9ChartInf.adjoin_inv_eq N k]
    exact hfd
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := by
    rw [JacJ9ChartInf.adjoin_inv_eq N k]
    exact hsep
  haveI : IsDedekindDomain
      (CurveModel.chartRing k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N))) :=
    IsIntegralClosure.isDedekindDomain
      (Algebra.adjoin k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (IntermediateField.adjoin k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) _
  haveI : IsFractionRing
      (CurveModel.chartRing k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      (Algebra.adjoin k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (IntermediateField.adjoin k ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) _

  have hw : ∀ r : CurveModel.chartRing k
      ({(JacJ9ChartInf.jt k N)⁻¹} : Set (modularFunctionFieldC k N)),
      algebraMap _ (modularFunctionFieldC k N) r ∈ v.toValuationSubring :=
    fun r => CurveModel.chartRing_le_valuationSubring v.toValuationSubring v.algebraMap_mem'
      (Set.singleton_subset_iff.mpr hjinv) r.2
  have heq := v.toValuationSubring_eq_of_forall_mem hw
  have hg' : g ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (modularFunctionFieldC k N) (v.centerHeightOneSpectrum _ hw) := heq ▸ hg
  obtain ⟨a, s, hs, hga⟩ := hg'
  have hs' : s ∉ v.center _ hw := Ideal.mem_primeCompl_iff.mp hs
  obtain ⟨b, hb⟩ :=
    (JacJ9ChartInf.mem_chartRing_iff_exists fm (a : modularFunctionFieldC k N)).mp a.2
  obtain ⟨b', hb'⟩ :=
    (JacJ9ChartInf.mem_chartRing_iff_exists fm (s : modularFunctionFieldC k N)).mp s.2
  have hs0 : (s : modularFunctionFieldC k N) ≠ 0 := by
    intro h0
    apply hs'
    have hsz : s = 0 := Subtype.ext h0
    rw [hsz]
    exact Ideal.zero_mem _
  refine ⟨b, b', ?_, ?_⟩
  ·
    rintro ⟨h, hres⟩
    rw [map_zero, IsLocalRing.residue_eq_zero_iff] at hres
    apply hs'
    refine (v.mem_center_iff hw).mpr ?_
    have hmk : (⟨algebraMap _ (modularFunctionFieldC k N) s, hw s⟩ : v.toValuationSubring) =
        ⟨fm.piInf b', h⟩ :=
      Subtype.ext hb'.symm
    rw [hmk]
    exact hres
  · rw [hga, hb, hb']
    exact inv_mul_cancel_right₀ hs0 _

end S_ModularCurve_CharPModel_FibreModel_piInf_range_localizes_of_not_affine
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_piInf_range_localizes_of_not_affine (solution)
