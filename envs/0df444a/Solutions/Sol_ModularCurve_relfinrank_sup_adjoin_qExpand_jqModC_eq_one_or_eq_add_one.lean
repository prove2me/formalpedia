-- Prove2me | solution 1 for ModularCurve.relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1f2ccf90-15b4-512a-a0b0-0ffd14a3401b

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModularEquationQ
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000

p2m_open "ModularCurve~dedekindPsi_prime~coeffMap_qExpand~coeffMap_injective Polynomial"

namespace Conj

theorem dedekindPsi_prime (ℓ : ℕ) [Fact ℓ.Prime] : dedekindPsi ℓ = ℓ + 1 := by
  have hp : ℓ.Prime := Fact.out
  rw [dedekindPsi, Nat.Prime.divisors hp]
  have h1 : Squarefree 1 := squarefree_one
  have hℓ : Squarefree ℓ := hp.squarefree
  rw [Finset.filter_insert, if_pos h1, Finset.filter_singleton, if_pos hℓ,
    Finset.sum_insert (by simp [hp.one_lt.ne]), Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos, add_comm]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

section Core

noncomputable abbrev Rram (L : Type*) [Field L] (ζ : Lˣ) (c : ℕ) : LaurentSeries L := qTwist (ζ ^ c) (jqModC L)

noncomputable abbrev Runr (L : Type*) [Field L] (ℓ : ℕ) [NeZero ℓ] : LaurentSeries L :=
  haveI : NeZero (ℓ * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ)⟩
  qExpand L (ℓ * ℓ) (jqModC L)

variable (L : Type*) [Field L] {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ] (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ ℓ) (data : ModularPolynomialData ℓ)

theorem core (hζ : IsPrimitiveRoot ζ ℓ) (g : Polynomial (LaurentSeries L)) (hg : g.Monic)
    (hdvd : g ∣ data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (qExpand L ℓ (jqModC L))))
    (hfix : g.map (qTwist ζ) = g) (hroot : g.IsRoot (Runr L ℓ)) :
    g.natDegree = 1 ∨ g.natDegree = ℓ + 1 := by
  classical
  have hp : ℓ.Prime := Fact.out
  obtain ⟨-, hsplit, hsep, hroots⟩ := ModularPolynomialData.map_adjoin_jqNModC_eq_cosetTwoVarPoly L ℓ data ζ hζ
  set Ψ := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (qExpand L ℓ (jqModC L))) with hΨ
  have hΨmap : (data.toJqNField L).map (algebraMap (jqNField L ℓ) (LaurentSeries L)) = Ψ :=
    ModularPolynomialData.toJqNField_map data L
  rw [hΨmap] at hsplit
  have hΨmonic : Ψ.Monic := data.monic.map _
  have hΨ0 : Ψ ≠ 0 := hΨmonic.ne_zero
  have hΨsep : Ψ.Separable := by rw [← hΨmap]; exact hsep.map
  have gsplit : g.Splits := Polynomial.Splits.of_dvd hsplit hΨ0 hdvd
  have gsep : g.Separable := hΨsep.of_dvd hdvd
  have g0 : g ≠ 0 := hg.ne_zero

  have hrootform : ∀ r, g.IsRoot r → r = Runr L ℓ ∨ ∃ c, r = Rram L ζ c := by
    intro r hr
    have hrΨ : Ψ.IsRoot r := by
      obtain ⟨h, hh⟩ := hdvd
      rw [Polynomial.IsRoot, hh, Polynomial.eval_mul, hr.eq_zero, zero_mul]
    have hmem : r ∈ (data.toJqNField L).rootSet (LaurentSeries L) := by
      rw [Polynomial.mem_rootSet']
      refine ⟨Polynomial.map_monic_ne_zero (data.toJqNField_monic L), ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hΨmap]
      exact hrΨ
    rw [hroots] at hmem
    obtain ⟨⟨a, b, d⟩, ht, rfl⟩ := hmem
    obtain ⟨had, hbd, -⟩ := (mem_primCosetReps hp.ne_zero).mp (Finset.mem_coe.mp ht)
    have ha : a = 1 ∨ a = ℓ := (Nat.dvd_prime hp).mp ⟨d, had.symm⟩
    rcases ha with rfl | rfl
    · right
      refine ⟨b, ?_⟩
      rw [cosetConj_eq, cosetSubst, RingHom.coe_comp, Function.comp_apply,
        qExpand_congr (show 1 * 1 = 1 by norm_num), qExpand_one_apply, one_mul]
    · left
      have hd : d = 1 := by
        have := had; rw [Nat.mul_eq_left hp.ne_zero] at this; exact this
      subst hd
      have hb : b = 0 := by omega
      subst hb
      rw [cosetConj_eq, cosetSubst, RingHom.coe_comp, Function.comp_apply, mul_zero, pow_zero, qTwist_one_apply]

  have hstab : ∀ r, g.IsRoot r → g.IsRoot (qTwist ζ r) := by
    intro r hr
    have := Polynomial.IsRoot.map (f := qTwist ζ) hr
    rwa [hfix] at this
  have hshift : ∀ c, qTwist ζ (Rram L ζ c) = Rram L ζ (c + 1) := by
    intro c
    show qTwist ζ (qTwist (ζ ^ c) (jqModC L)) = qTwist (ζ ^ (c + 1)) (jqModC L)
    rw [qTwist_qTwist, pow_succ, mul_comm]

  by_cases hram : ∃ c, g.IsRoot (Rram L ζ c)
  · right
    obtain ⟨c₀, hc₀⟩ := hram
    have hall : ∀ k, g.IsRoot (Rram L ζ (c₀ + k)) := by
      intro k
      induction k with
      | zero => simpa using hc₀
      | succ k ih => rw [← add_assoc, ← hshift]; exact hstab _ ih
    have hper : ∀ n m, Rram L ζ (n + ℓ * m) = Rram L ζ n := by
      intro n m
      show qTwist (ζ ^ (n + ℓ * m)) (jqModC L) = qTwist (ζ ^ n) (jqModC L)
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hallc : ∀ c, g.IsRoot (Rram L ζ c) := by
      intro c
      have h := hall (c + ℓ * c₀ - c₀)
      have hle : c₀ ≤ c + ℓ * c₀ := by nlinarith [hp.one_lt]
      rw [← Nat.add_sub_assoc hle, Nat.add_sub_cancel_left, hper] at h
      exact h

    have hΨroots : ∀ r, Ψ.IsRoot r → g.IsRoot r := by
      intro r hr
      have hmem : r ∈ (data.toJqNField L).rootSet (LaurentSeries L) := by
        rw [Polynomial.mem_rootSet']
        refine ⟨Polynomial.map_monic_ne_zero (data.toJqNField_monic L), ?_⟩
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hΨmap]
        exact hr
      rw [hroots] at hmem
      obtain ⟨⟨a, b, d⟩, ht, rfl⟩ := hmem
      obtain ⟨had, hbd, -⟩ := (mem_primCosetReps hp.ne_zero).mp (Finset.mem_coe.mp ht)
      have ha : a = 1 ∨ a = ℓ := (Nat.dvd_prime hp).mp ⟨d, had.symm⟩
      rcases ha with rfl | rfl
      · have := hallc b
        rwa [show Rram L ζ b = cosetConj ζ (jqModC L) (1, b, d) by
          rw [cosetConj_eq, cosetSubst, RingHom.coe_comp, Function.comp_apply,
            qExpand_congr (show 1 * 1 = 1 by norm_num), qExpand_one_apply, one_mul]] at this
      · have hd : d = 1 := by
          have := had; rw [Nat.mul_eq_left hp.ne_zero] at this; exact this
        subst hd
        have hb : b = 0 := by omega
        subst hb
        rw [cosetConj_eq, cosetSubst, RingHom.coe_comp, Function.comp_apply, mul_zero, pow_zero, qTwist_one_apply]
        exact hroot
    have hle1 : g.roots ≤ Ψ.roots := Polynomial.roots.le_of_dvd hΨ0 hdvd
    have hle2 : Ψ.roots ≤ g.roots := by
      rw [Multiset.le_iff_subset (Polynomial.nodup_roots hΨsep)]
      intro r hr
      exact (Polynomial.mem_roots g0).mpr (hΨroots r ((Polynomial.mem_roots hΨ0).mp hr))
    have heq : g.roots = Ψ.roots := le_antisymm hle1 hle2
    rw [Polynomial.Splits.natDegree_eq_card_roots gsplit, heq, ← Polynomial.Splits.natDegree_eq_card_roots hsplit,
      hΨ, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime]
  · left
    simp only [not_exists] at hram
    have hsub : ∀ r ∈ g.roots, r = Runr L ℓ := by
      intro r hr
      rcases hrootform r ((Polynomial.mem_roots g0).mp hr) with h | ⟨c, rfl⟩
      · exact h
      · exact absurd ((Polynomial.mem_roots g0).mp hr) (hram c)
    have hle : g.roots ≤ {Runr L ℓ} :=
      (Multiset.le_iff_subset (Polynomial.nodup_roots gsep)).mpr (fun r hr => Multiset.mem_singleton.mpr (hsub r hr))
    have hcard : g.roots.card ≤ 1 := by simpa using Multiset.card_le_card hle
    have hpos : 0 < g.roots.card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨_, (Polynomial.mem_roots g0).mpr hroot⟩
    rw [Polynomial.Splits.natDegree_eq_card_roots gsplit]
    omega

end Core

end Conj

theorem solution
    (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : K) ≠ 0)
    (F : IntermediateField K (LaurentSeries K)) (hj : jqModC K ∈ F) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    IntermediateField.relfinrank F (F ⊔ IntermediateField.adjoin K {qExpand K ℓ (jqModC K)}) = 1 ∨
      IntermediateField.relfinrank F (F ⊔ IntermediateField.adjoin K {qExpand K ℓ (jqModC K)}) = ℓ + 1 := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero ((ℓ : ℕ) : K) := ⟨hℓ⟩
  have hp : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData ℓ
  set y : LaurentSeries K := qExpand K ℓ (jqModC K) with hydef
  let jF : F := ⟨jqModC K, hj⟩

  let P : Polynomial F := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) jF)
  have hPmonic : P.Monic := data.monic.map _
  have hPmap : P.map (algebraMap F (LaurentSeries K)) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K)) := by
    rw [Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_X]
    rfl
  have hPy : Polynomial.aeval y P = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hPmap, Polynomial.eval_map]
    have h1 := ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero data K 1
    have e1 : jqNModC K 1 = jqModC K := qExpand_one_apply _
    have e2 : jqNModC K (1 * ℓ) = y := qExpand_congr (one_mul ℓ) _
    rw [e1, e2] at h1
    have e3 : (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K)) =
        (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom := by
      apply RingHom.ext; intro q
      rw [Polynomial.coe_eval₂RingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_def,
        RingHom.ext_int (algebraMap ℤ (LaurentSeries K)) (Int.castRingHom _)]
    rw [e3]; exact h1
  have hint : IsIntegral F y := ⟨P, hPmonic, by rwa [Polynomial.aeval_def] at hPy⟩
  have hmdvd : minpoly F y ∣ P := minpoly.dvd F y hPy

  have hζ := IsCyclotomicExtension.zeta_spec ℓ K (CyclotomicField ℓ K)
  have hζ0 : IsCyclotomicExtension.zeta ℓ K (CyclotomicField ℓ K) ≠ 0 := hζ.ne_zero hp.ne_zero
  let ζ : (CyclotomicField ℓ K)ˣ := Units.mk0 _ hζ0
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp (by simpa [ζ] using hζ)
  let ι : K →+* CyclotomicField ℓ K := algebraMap K (CyclotomicField ℓ K)
  let φ : LaurentSeries K →+* LaurentSeries (CyclotomicField ℓ K) := (qExpand (CyclotomicField ℓ K) ℓ).comp (coeffMap ι)
  have hφ : ∀ x, φ x = qExpand (CyclotomicField ℓ K) ℓ (coeffMap ι x) := fun _ => rfl
  have hιj : coeffMap ι (jqModC K) = jqModC (CyclotomicField ℓ K) := by
    ext k; rw [coeffMap_coeff, ← map_jqModC ι, HahnSeries.map_coeff]
  have hφj : φ (jqModC K) = qExpand (CyclotomicField ℓ K) ℓ (jqModC (CyclotomicField ℓ K)) := by rw [hφ, hιj]
  have hφy : φ y = Conj.Runr (CyclotomicField ℓ K) ℓ := by
    rw [hφ, hydef, Conj.coeffMap_qExpand, hιj, qExpand_qExpand]
  let ψ : F →+* LaurentSeries (CyclotomicField ℓ K) := φ.comp (algebraMap F (LaurentSeries K))
  set g : Polynomial (LaurentSeries (CyclotomicField ℓ K)) := (minpoly F y).map ψ with hgdef
  have hgmonic : g.Monic := (minpoly.monic hint).map ψ
  have hgdeg : g.natDegree = (minpoly F y).natDegree := (minpoly.monic hint).natDegree_map ψ

  have hΨ : P.map ψ = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (CyclotomicField ℓ K)))
      (qExpand (CyclotomicField ℓ K) ℓ (jqModC (CyclotomicField ℓ K)))) := by
    show (data.Φ.map _).map ψ = _
    rw [Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_X]
    show φ (algebraMap F (LaurentSeries K) jF) = _
    exact hφj
  have hgdvd : g ∣ data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (CyclotomicField ℓ K)))
      (qExpand (CyclotomicField ℓ K) ℓ (jqModC (CyclotomicField ℓ K)))) := by
    rw [← hΨ, hgdef]; exact Polynomial.map_dvd ψ hmdvd

  have hσφ : ∀ x, qTwist ζ (φ x) = φ x := by
    intro x
    rw [hφ, qTwist_qExpand, show ζ ^ ((ℓ : ℕ) : ℤ) = 1 by rw [zpow_natCast, hζu.pow_eq_one], qTwist_one_apply]
  have hgfix : g.map (qTwist ζ) = g := by
    rw [hgdef, Polynomial.map_map]
    congr 1
    apply RingHom.ext; intro a
    exact hσφ _

  have hgroot : g.IsRoot (Conj.Runr (CyclotomicField ℓ K) ℓ) := by
    rw [← hφy, hgdef, show (minpoly F y).map ψ = ((minpoly F y).map (algebraMap F (LaurentSeries K))).map φ by rw [Polynomial.map_map]]
    apply Polynomial.IsRoot.map
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval F y
  have hcore := Conj.core (CyclotomicField ℓ K) ζ data hζu g hgmonic hgdvd hgfix hgroot

  have hrel : IntermediateField.relfinrank F (F ⊔ IntermediateField.adjoin K {y}) = (minpoly F y).natDegree := by
    have hle : F ≤ F ⊔ IntermediateField.adjoin K {y} := le_sup_left
    rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
    have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin F {y} := by
      apply le_antisymm
      · intro x hx
        rw [IntermediateField.mem_extendScalars] at hx

        have hsub : F ⊔ IntermediateField.adjoin K {y} ≤ (IntermediateField.adjoin F {y}).restrictScalars K := by
          refine sup_le ?_ ?_
          · intro z hz
            exact (IntermediateField.adjoin F {y}).algebraMap_mem ⟨z, hz⟩
          · rw [IntermediateField.adjoin_le_iff]
            intro z hz
            exact IntermediateField.subset_adjoin F ({y} : Set (LaurentSeries K)) hz
        exact hsub hx
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        show y ∈ IntermediateField.extendScalars hle
        rw [IntermediateField.mem_extendScalars]
        exact le_sup_right (b := IntermediateField.adjoin K {y}) (IntermediateField.mem_adjoin_simple_self K y)
    rw [hext]
    exact IntermediateField.adjoin.finrank hint
  rw [hrel, ← hgdeg]
  exact hcore

end S_ModularCurve_relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one
end P2MW
export P2MW.S_ModularCurve_relfinrank_sup_adjoin_qExpand_jqModC_eq_one_or_eq_add_one (solution)
