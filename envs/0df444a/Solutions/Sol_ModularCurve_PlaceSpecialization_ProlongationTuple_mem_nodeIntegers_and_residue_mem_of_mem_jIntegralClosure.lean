-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b276d626-48b9-5539-83ef-91a12571765f

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_jqNModC_mul_eq_pow
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace VbH0

section Transport

variable {L : Type*} [Field L]

def inclHom (S : Subring (LaurentSeries L)) (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F) (hSO : ∀ s : LaurentSeries L, s ∈ S → ∃ hF : s ∈ F, (⟨s, hF⟩ : F) ∈ O) : S →+* O where
  toFun s := ⟨⟨(s : LaurentSeries L), (hSO s s.2).1⟩, (hSO s s.2).2⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

theorem coe_coe_inclHom (S : Subring (LaurentSeries L)) (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F) (hSO : ∀ s : LaurentSeries L, s ∈ S → ∃ hF : s ∈ F, (⟨s, hF⟩ : F) ∈ O) (s : S) :
    (((inclHom S F O hSO s : O) : F) : LaurentSeries L) = (s : LaurentSeries L) := rfl

theorem exists_monic_eval_eq_zero (S : Subring (LaurentSeries L)) (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F) (hSO : ∀ s : LaurentSeries L, s ∈ S → ∃ hF : s ∈ F, (⟨s, hF⟩ : F) ∈ O)
    (t : F) (ht : IsIntegral S (t : LaurentSeries L)) :
    ∃ Q : Polynomial O, Q.Monic ∧ Polynomial.eval₂ (algebraMap O F) t Q = 0 := by
  obtain ⟨p, hpm, hp⟩ := ht
  refine ⟨p.map (inclHom S F O hSO), hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hinj : Function.Injective (fun x : F => (x : LaurentSeries L)) := Subtype.val_injective
  apply hinj
  show ((Polynomial.eval₂ ((algebraMap O F).comp (inclHom S F O hSO)) t p : F) : LaurentSeries L) =
    ((0 : F) : LaurentSeries L)
  rw [ZeroMemClass.coe_zero]
  have h := Polynomial.hom_eval₂ p ((algebraMap O F).comp (inclHom S F O hSO)) (F.val.toRingHom) t
  have hcomp : (F.val.toRingHom).comp ((algebraMap O F).comp (inclHom S F O hSO)) = algebraMap S (LaurentSeries L) := by
    ext s; rfl
  rw [hcomp] at h
  exact h.trans hp

theorem mem_of_isIntegral (S : Subring (LaurentSeries L)) (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F) (hSO : ∀ s : LaurentSeries L, s ∈ S → ∃ hF : s ∈ F, (⟨s, hF⟩ : F) ∈ O)
    (t : F) (ht : IsIntegral S (t : LaurentSeries L)) : t ∈ O := by
  obtain ⟨Q, hQm, hQ⟩ := exists_monic_eval_eq_zero S F O hSO t ht
  have hint : IsIntegral O t := ⟨Q, hQm, hQ⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

theorem mem_of_monic_coeff_mem {E : Type*} [Field E] (O' : ValuationSubring E) (Q : Polynomial E)
    (hQ : Q.Monic) (hcoeff : ∀ i : ℕ, Q.coeff i ∈ O') (x : E) (hx : Q.eval x = 0) : x ∈ O' := by
  have hl : Q ∈ Polynomial.lifts (algebraMap O' E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n; exact ⟨⟨Q.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨Q', hQ', -, hQ'm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hQ
  have hint : IsIntegral O' x := by
    refine ⟨Q', hQ'm, ?_⟩
    rw [← Polynomial.eval_map, hQ']
    exact hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]; exact y.2

theorem apply_mem_of_isIntegral (S : Subring (LaurentSeries L)) (F : IntermediateField L (LaurentSeries L))
    (O : ValuationSubring F) (hSO : ∀ s : LaurentSeries L, s ∈ S → ∃ hF : s ∈ F, (⟨s, hF⟩ : F) ∈ O)
    (t : F) (ht : IsIntegral S (t : LaurentSeries L)) (htO : t ∈ O)
    {E : Type*} [Field E] (ρ : O →+* E) (O' : ValuationSubring E)
    (hρ : ∀ s : LaurentSeries L, ∀ hs : s ∈ S, ρ (inclHom S F O hSO ⟨s, hs⟩) ∈ O') :
    ρ ⟨t, htO⟩ ∈ O' := by
  obtain ⟨p, hpm, hp⟩ := ht
  set q : Polynomial O := p.map (inclHom S F O hSO) with hq
  have hqm : q.Monic := hpm.map _

  have hroot : q.eval ⟨t, htO⟩ = 0 := by
    have hinj : Function.Injective (fun x : O => (((x : O) : F) : LaurentSeries L)) :=
      fun a b h => Subtype.ext (Subtype.ext h)
    apply hinj
    show ((((q.eval ⟨t, htO⟩ : O) : F) : LaurentSeries L)) = (((0 : O) : F) : LaurentSeries L)
    have h1 := Polynomial.hom_eval₂ p (inclHom S F O hSO) ((F.val.toRingHom).comp (algebraMap O F)) ⟨t, htO⟩
    have hcomp : ((F.val.toRingHom).comp (algebraMap O F)).comp (inclHom S F O hSO) = algebraMap S (LaurentSeries L) := by
      ext s; rfl
    rw [hcomp, ← Polynomial.eval_map] at h1
    rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
    exact h1.trans hp

  refine mem_of_monic_coeff_mem O' (q.map ρ) (hqm.map ρ) (fun i => ?_) (ρ ⟨t, htO⟩) ?_
  · rw [Polynomial.coeff_map, hq, Polynomial.coeff_map]
    exact hρ _ (p.coeff i).2
  · rw [Polynomial.eval_map, Polynomial.eval₂_hom, hroot, map_zero]

end Transport

end VbH0

namespace VbH0

section Modular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

local notation "Lb" => AlgebraicClosure ℚ
local notation "Fq" => modularFunctionFieldBar (N * q)

noncomputable def jBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem coe_jFun : ((ProlongationTuple.jFun N q : Fq) : LaurentSeries Lb) = jqModC Lb := coeffEmb_jq Lb

theorem heckeAlphaBar_jBar : heckeAlphaBar Lb N q (jBarN N) = ProlongationTuple.jFun N q := by
  apply Subtype.ext; rw [coe_heckeAlphaBar]; rfl

theorem atkinLehnerBar_jFun (hqN : ¬ q ∣ N) :
    atkinLehnerBar N q (ProlongationTuple.jFun N q) = heckeBetaBar Lb N q (jBarN N) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out) hqN)
  have h := (geomAut_atkinLehner_comp_legs Lb N q (atkinLehnerInvolutionFull N q) hσ).1
  have h' := congrArg (fun φ : _ →ₐ[Lb] _ => φ (jBarN N)) h
  simp only [AlgHom.comp_apply] at h'
  rw [← heckeAlphaBar_jBar]
  exact h'

theorem coe_heckeBetaBar_jBar :
    ((heckeBetaBar Lb N q (jBarN N) : Fq) : LaurentSeries Lb) = jqNModC Lb q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [coe_heckeBetaBar]
  show qExpand Lb q (coeffEmb Lb jq) = _
  rw [coeffEmb_jq]; rfl

theorem jRing_subset (K : IntermediateField ℚ Lb) (O : ValuationSubring Fq)
    (hconst : ∀ c : coeffSubring A K, (algebraMap Lb Fq (c : Lb) : Fq) ∈ O)
    (hj : (ProlongationTuple.jFun N q : Fq) ∈ O) :
    ∀ s : LaurentSeries Lb, s ∈ jRing A K → ∃ hF : s ∈ Fq, (⟨s, hF⟩ : Fq) ∈ O := by
  intro s hs
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | hx
    · exact ⟨(algebraMap Lb Fq (c : Lb)).2, hconst c⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      have hF : jqModC Lb ∈ Fq := by rw [← coe_jFun (N := N) (q := q)]; exact (ProlongationTuple.jFun N q).2
      refine ⟨hF, ?_⟩
      have h : (⟨jqModC Lb, hF⟩ : Fq) = ProlongationTuple.jFun N q := Subtype.ext (coe_jFun (N := N) (q := q)).symm
      rw [h]; exact hj
  | zero => exact ⟨zero_mem _, zero_mem O⟩
  | one => exact ⟨one_mem _, one_mem O⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨hx, hxO⟩ := ihx; obtain ⟨hy, hyO⟩ := ihy
    refine ⟨add_mem hx hy, ?_⟩
    have he : (⟨x + y, add_mem hx hy⟩ : Fq) = ⟨x, hx⟩ + ⟨y, hy⟩ := Subtype.ext rfl
    rw [he]; exact add_mem hxO hyO
  | neg x _ ihx =>
    obtain ⟨hx, hxO⟩ := ihx
    refine ⟨neg_mem hx, ?_⟩
    have he : (⟨-x, neg_mem hx⟩ : Fq) = -⟨x, hx⟩ := Subtype.ext rfl
    rw [he]; exact neg_mem hxO
  | mul x y _ _ ihx ihy =>
    obtain ⟨hx, hxO⟩ := ihx; obtain ⟨hy, hyO⟩ := ihy
    refine ⟨mul_mem hx hy, ?_⟩
    have he : (⟨x * y, mul_mem hx hy⟩ : Fq) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
    rw [he]; exact mul_mem hxO hyO

theorem jFun_mem_integersFst_and_residue₁ :
    ∃ h : (ProlongationTuple.jFun N q : Fq) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = jGeomGen k N := by
  have hy : coeffMap A.subtype (jqModC A) ∈ Fq := by
    rw [coeffSemilinearAut.coeffMap_jqModC, ← coe_jFun (N := N) (q := q)]; exact SetLike.coe_mem _
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (jqModC A) hy
  have helt : (⟨coeffMap A.subtype (jqModC A), hy⟩ : Fq) = ProlongationTuple.jFun N q := by
    apply Subtype.ext
    show coeffMap A.subtype (jqModC A) = _
    rw [coeffSemilinearAut.coeffMap_jqModC, coe_jFun]
  refine ⟨helt ▸ h, ?_⟩
  have : (⟨ProlongationTuple.jFun N q, helt ▸ h⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype (jqModC A), hy⟩, h⟩ := by
    apply Subtype.ext; exact helt.symm
  rw [this, R.residue₁_apply]
  apply Subtype.ext
  rw [R.ι_coe, hres, coeffSemilinearAut.coeffMap_jqModC, coeffSemilinearAut.coeffMap_jqModC]
  rfl

theorem heckeBetaBar_jBar_mem_integersFst_and_residue₁ :
    ∃ h : (heckeBetaBar Lb N q (jBarN N) : Fq) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = jGeomGen k N ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hy : coeffMap A.subtype (jqNModC A q) ∈ Fq := by
    rw [coeffSemilinearAut.coeffMap_jqNModC, ← coe_heckeBetaBar_jBar (N := N) (q := q)]; exact SetLike.coe_mem _
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (jqNModC A q) hy
  have helt : (⟨coeffMap A.subtype (jqNModC A q), hy⟩ : Fq) = heckeBetaBar Lb N q (jBarN N) := by
    apply Subtype.ext
    show coeffMap A.subtype (jqNModC A q) = _
    rw [coeffSemilinearAut.coeffMap_jqNModC, coe_heckeBetaBar_jBar]
  refine ⟨helt ▸ h, ?_⟩
  have : (⟨heckeBetaBar Lb N q (jBarN N), helt ▸ h⟩ : R.R₁.integers) =
      ⟨⟨coeffMap A.subtype (jqNModC A q), hy⟩, h⟩ := by
    apply Subtype.ext; exact helt.symm
  rw [this, R.residue₁_apply]
  apply Subtype.ext
  rw [R.ι_coe, hres, coeffSemilinearAut.coeffMap_jqNModC, coeffSemilinearAut.coeffMap_jqNModC,
    SubmonoidClass.coe_pow]
  show jqNModC k q = (jqModC k) ^ q
  have h1 := jqNModC_mul_eq_pow k 1 (ℓ := q)
  rw [jqNModC_one] at h1
  simpa only [one_mul] using h1

theorem jFun_mem_integersSnd_and_residue₂ (hqN : ¬ q ∣ N) :
    ∃ h : (ProlongationTuple.jFun N q : Fq) ∈ R.R₂.integers,
      R.residue₂ ⟨_, h⟩ = jGeomGen k N ^ q := by
  obtain ⟨h₁, hres⟩ := heckeBetaBar_jBar_mem_integersFst_and_residue₁ (N := N) R
  have h₂ : (ProlongationTuple.jFun N q : Fq) ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, atkinLehnerBar_jFun hqN]; exact h₁
  refine ⟨h₂, ?_⟩
  rw [R.residue₂_apply, R.residue₂_eq]
  have key : ∀ h' : atkinLehnerBar N q (ProlongationTuple.jFun N q) ∈ R.R₁.integers,
      R.ι (R.R₁.residue ⟨_, h'⟩) = jGeomGen k N ^ q := by
    intro h'
    have helt : (⟨atkinLehnerBar N q (ProlongationTuple.jFun N q), h'⟩ : R.R₁.integers) =
        ⟨heckeBetaBar Lb N q (jBarN N), h₁⟩ := Subtype.ext (atkinLehnerBar_jFun hqN)
    rw [helt, ← R.residue₁_apply, hres]
  exact key _

theorem residue₁_const (c : A) :
    ∃ h : (algebraMap Lb Fq (c : Lb) : Fq) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red c) := by
  refine ⟨(R.R₁.algebraMap_mem_iff (c : Lb)).mpr c.2, ?_⟩
  rw [R.residue₁_apply, R.R₁.residue_algebraMap c]
  apply Subtype.ext
  rw [R.ι_coe]
  show coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A c))
    = algebraMap k (LaurentSeries k) (red c)
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue, algebraMap_laurentSeries_eq_single]

theorem residue₂_const (c : A) :
    ∃ h : (algebraMap Lb Fq (c : Lb) : Fq) ∈ R.R₂.integers,
      R.residue₂ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red c) := by
  refine ⟨(R.R₂.algebraMap_mem_iff (c : Lb)).mpr c.2, ?_⟩
  rw [R.residue₂_apply, R.R₂.residue_algebraMap c]
  apply Subtype.ext
  rw [R.ι_coe]
  show coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A c))
    = algebraMap k (LaurentSeries k) (red c)
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue, algebraMap_laurentSeries_eq_single]

theorem jBarN_mem_place (u : Place Lb (modularFunctionFieldBar N))
    (hu : jGeomGen k N ∈ (P.sp u).toValuationSubring) :
    jBarN N ∈ u.toValuationSubring := by
  have hnonneg : 0 ≤ (P.sp u).ord (jGeomGen k N) := (P.sp u).ord_nonneg_of_mem hu
  have hnot : ¬ ∀ a : A, u.ord (jBarN N - algebraMap Lb (modularFunctionFieldBar N) (a : Lb)) ≤ 0 := by
    intro hall
    exact absurd (P.d0_j_pole u hall) (not_lt.mpr hnonneg)
  obtain ⟨a, ha⟩ : ∃ a : A, 0 < u.ord (jBarN N - algebraMap Lb (modularFunctionFieldBar N) (a : Lb)) := by
    by_contra h
    apply hnot
    intro a
    by_contra h'
    exact h ⟨a, lt_of_not_ge h'⟩
  have hne : jBarN N - algebraMap Lb (modularFunctionFieldBar N) (a : Lb) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have hmem := u.mem_of_ord_nonneg hne ha.le
  have := add_mem hmem (u.algebraMap_mem' (a : Lb))
  rwa [sub_add_cancel] at this

theorem restrictAlong_mem_iff' {K₀ E E' : Type*} [Field K₀] [Field E] [Field E'] [Algebra K₀ E] [Algebra K₀ E']
    (φ : E →ₐ[K₀] E') (hφ : φ.toRingHom.IsIntegral) (W : Place K₀ E') (f : E) :
    f ∈ (W.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ W.toValuationSubring := Iff.rfl

theorem jFun_mem_place {V : Place Lb Fq}
    (hV : jGeomGen k N ∈ (P.sp (V.restrictAlong (heckeAlphaBar Lb N q) hα)).toValuationSubring) :
    (ProlongationTuple.jFun N q : Fq) ∈ V.toValuationSubring := by
  have h2 : heckeAlphaBar Lb N q (jBarN N) ∈ V.toValuationSubring :=
    (restrictAlong_mem_iff' (heckeAlphaBar Lb N q) hα V (jBarN N)).mp (jBarN_mem_place (P := P) _ hV)
  rwa [heckeAlphaBar_jBar] at h2

end Modular
end VbH0

open VbH0 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    t ∈ R.nodeIntegers w ∧
    (∀ h₁ : t ∈ R.R₁.integers, (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring) ∧
    (∀ h₂ : t ∈ R.R₂.integers,
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) ∈ (arithFrobC q k N • w).toValuationSubring) := by
  have hint : IsIntegral (jRing A K) (t : LaurentSeries (AlgebraicClosure ℚ)) := ht.2
  have haff : IsAffineGeomPlace k N w := hw.2.1
  have hw' : arithFrobC q k N • w ∈ ssPlaces q N k := arithFrobC_smul_mem_ssPlaces_univ q N k w hw
  have haff' : IsAffineGeomPlace k N (arithFrobC q k N • w) := hw'.2.1

  obtain ⟨hj₁, hjres₁⟩ := jFun_mem_integersFst_and_residue₁ (N := N) (q := q) R
  obtain ⟨hj₂, hjres₂⟩ := jFun_mem_integersSnd_and_residue₂ (N := N) R hqN
  have hS₁ := jRing_subset (N := N) (q := q) (A := A) K R.R₁.integers
    (fun c => (R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2.1) hj₁
  have hS₂ := jRing_subset (N := N) (q := q) (A := A) K R.R₂.integers
    (fun c => (R.R₂.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2.1) hj₂
  have ht₁ : t ∈ R.R₁.integers := mem_of_isIntegral _ _ _ hS₁ t hint
  have ht₂ : t ∈ R.R₂.integers := mem_of_isIntegral _ _ _ hS₂ t hint
  refine ⟨⟨ht₁, ht₂, fun V hV => ?_⟩, fun h₁ => ?_, fun h₂ => ?_⟩
  · have hSV := jRing_subset (N := N) (q := q) (A := A) K V.toValuationSubring
      (fun c => V.algebraMap_mem' _) (jFun_mem_place (P := P) (by rw [show P.sp _ = w from hV]; exact haff.1))
    exact mem_of_isIntegral _ _ _ hSV t hint
  · refine apply_mem_of_isIntegral _ _ _ hS₁ t hint h₁ R.residue₁ w.toValuationSubring fun s hs => ?_

    induction hs using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | hx
      · obtain ⟨hc, hcres⟩ := residue₁_const (N := N) (q := q) R ⟨(c : AlgebraicClosure ℚ), c.2.1⟩
        have : inclHom (jRing A K) _ R.R₁.integers hS₁ ⟨_, Subring.subset_closure (Or.inl ⟨c, rfl⟩)⟩ = ⟨_, hc⟩ :=
          Subtype.ext (Subtype.ext rfl)
        rw [this, hcres]; exact w.algebraMap_mem' _
      · rw [Set.mem_singleton_iff] at hx; subst hx
        have : inclHom (jRing A K) _ R.R₁.integers hS₁ ⟨_, Subring.subset_closure (Or.inr rfl)⟩ = ⟨_, hj₁⟩ :=
          Subtype.ext (Subtype.ext (coe_jFun (N := N) (q := q)).symm)
        rw [this, hjres₁]; exact haff.1
    | zero => show R.residue₁ (inclHom _ _ _ hS₁ 0) ∈ _; rw [map_zero, map_zero]; exact zero_mem _
    | one => show R.residue₁ (inclHom _ _ _ hS₁ 1) ∈ _; rw [map_one, map_one]; exact one_mem _
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subring.add_mem _ hx hy⟩ : jRing A K) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add]; exact add_mem ihx ihy
    | neg x hx ihx =>
      have : (⟨-x, Subring.neg_mem _ hx⟩ : jRing A K) = -⟨x, hx⟩ := rfl
      rw [this, map_neg, map_neg]; exact neg_mem ihx
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subring.mul_mem _ hx hy⟩ : jRing A K) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul]; exact mul_mem ihx ihy
  · refine apply_mem_of_isIntegral _ _ _ hS₂ t hint h₂ R.residue₂ (arithFrobC q k N • w).toValuationSubring
      fun s hs => ?_
    induction hs using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | hx
      · obtain ⟨hc, hcres⟩ := residue₂_const (N := N) (q := q) R ⟨(c : AlgebraicClosure ℚ), c.2.1⟩
        have : inclHom (jRing A K) _ R.R₂.integers hS₂ ⟨_, Subring.subset_closure (Or.inl ⟨c, rfl⟩)⟩ = ⟨_, hc⟩ :=
          Subtype.ext (Subtype.ext rfl)
        rw [this, hcres]; exact (arithFrobC q k N • w).algebraMap_mem' _
      · rw [Set.mem_singleton_iff] at hx; subst hx
        have : inclHom (jRing A K) _ R.R₂.integers hS₂ ⟨_, Subring.subset_closure (Or.inr rfl)⟩ = ⟨_, hj₂⟩ :=
          Subtype.ext (Subtype.ext (coe_jFun (N := N) (q := q)).symm)
        rw [this, hjres₂]; exact pow_mem haff'.1 q
    | zero => show R.residue₂ (inclHom _ _ _ hS₂ 0) ∈ _; rw [map_zero, map_zero]; exact zero_mem _
    | one => show R.residue₂ (inclHom _ _ _ hS₂ 1) ∈ _; rw [map_one, map_one]; exact one_mem _
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subring.add_mem _ hx hy⟩ : jRing A K) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add]; exact add_mem ihx ihy
    | neg x hx ihx =>
      have : (⟨-x, Subring.neg_mem _ hx⟩ : jRing A K) = -⟨x, hx⟩ := rfl
      rw [this, map_neg, map_neg]; exact neg_mem ihx
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subring.mul_mem _ hx hy⟩ : jRing A K) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul]; exact mul_mem ihx ihy

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure (solution)
