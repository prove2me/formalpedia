-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_levelAut_pow_eq_and_forall_eq_pow_blowupChart_of_eq_adjoin_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4cf905c9-77c1-58a8-9d5e-8e9e2993212d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_levelAut_pow_eq_and_forall_eq_pow_blowupChart_of_eq_adjoin_of_drinfeldChartWitness_linked
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace EndsCyclicLinkedSol

section Core

variable {G F : Type*} [Group G] [CommGroup F] [Finite F]

omit [Finite F] in

theorem pow_adm_and_rel (Adm : G → Prop) (R : G → F → Prop)
    (h1 : Adm 1) (hR1 : R 1 1)
    (hmul : ∀ τ τ', Adm τ → Adm τ' → Adm (τ * τ'))
    (hRmul : ∀ τ τ' c c', Adm τ → Adm τ' → R τ c → R τ' c' → R (τ * τ') (c * c'))
    {τ : G} {c : F} (hτ : Adm τ) (hc : R τ c) (k : ℕ) : Adm (τ ^ k) ∧ R (τ ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using ⟨h1, hR1⟩
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hmul _ _ ih.1 hτ, hRmul _ _ _ _ ih.1 hτ ih.2 hc⟩

theorem exists_generator_of_faithful_scalar [IsCyclicSubgroups : ∀ S : Subgroup F, IsCyclic S]
    (Adm : G → Prop) (R : G → F → Prop) (e : ℕ)
    (h1 : Adm 1) (hR1 : R 1 1)
    (hmul : ∀ τ τ', Adm τ → Adm τ' → Adm (τ * τ'))
    (hRmul : ∀ τ τ' c c', Adm τ → Adm τ' → R τ c → R τ' c' → R (τ * τ') (c * c'))
    (hex : ∀ τ, Adm τ → ∃ c, R τ c ∧ (τ ≠ 1 → c ≠ 1))
    (huniq : ∀ τ c c', Adm τ → R τ c → R τ c' → c = c')
    (hpow : ∀ τ c, Adm τ → R τ c → c ^ e = 1) :
    ∃ (n : ℕ) (τ₀ : G) (c₀ : F), 0 < n ∧ n ∣ e ∧ Adm τ₀ ∧ R τ₀ c₀ ∧ τ₀ ^ n = 1 ∧
      (∀ k : ℕ, 0 < k → k < n → ¬ R (τ₀ ^ k) 1) ∧
      (∀ τ, Adm τ → ∃ k : ℕ, k < n ∧ τ = τ₀ ^ k) := by
  classical

  have hfaith : ∀ τ, Adm τ → R τ 1 → τ = 1 := by
    intro τ hτ hR
    obtain ⟨c, hc, hne⟩ := hex τ hτ
    have hc1 : c = 1 := huniq τ c 1 hτ hc hR
    by_contra hτ1
    exact hne hτ1 hc1
  have hpw := fun {τ : G} {c : F} (hτ : Adm τ) (hc : R τ c) =>
    pow_adm_and_rel Adm R h1 hR1 hmul hRmul hτ hc

  let S : Subgroup F :=
    { carrier := {c | ∃ τ, Adm τ ∧ R τ c}
      one_mem' := ⟨1, h1, hR1⟩
      mul_mem' := by
        rintro c c' ⟨τ, hτ, hc⟩ ⟨τ', hτ', hc'⟩
        exact ⟨τ * τ', hmul _ _ hτ hτ', hRmul _ _ _ _ hτ hτ' hc hc'⟩
      inv_mem' := by
        rintro c ⟨τ, hτ, hc⟩
        refine ⟨τ ^ (orderOf c - 1), (hpw hτ hc _).1, ?_⟩
        have hinv : c⁻¹ = c ^ (orderOf c - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos c), pow_orderOf_eq_one]
        rw [hinv]
        exact (hpw hτ hc _).2 }
  haveI : IsCyclic S := IsCyclicSubgroups S
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  obtain ⟨τ₀, hτ₀, hR₀⟩ := g.2
  set c₀ : F := (g : F) with hc₀
  set n : ℕ := orderOf c₀ with hn
  have hn0 : 0 < n := orderOf_pos c₀

  have hτ₀n : τ₀ ^ n = 1 := by
    refine hfaith _ (hpw hτ₀ hR₀ n).1 ?_
    have := (hpw hτ₀ hR₀ n).2
    rwa [hn, pow_orderOf_eq_one] at this
  refine ⟨n, τ₀, c₀, hn0, ?_, hτ₀, hR₀, hτ₀n, ?_, ?_⟩
  ·
    exact orderOf_dvd_of_pow_eq_one (hpow τ₀ c₀ hτ₀ hR₀)
  ·
    intro k hk hkn hRk
    have hck : c₀ ^ k = 1 := (huniq _ _ _ (hpw hτ₀ hR₀ k).1 (hpw hτ₀ hR₀ k).2 hRk)
    have hdvd : n ∣ k := orderOf_dvd_of_pow_eq_one hck
    exact absurd (Nat.le_of_dvd hk hdvd) (not_le.mpr hkn)
  ·
    intro τ hτ
    obtain ⟨c, hc, -⟩ := hex τ hτ
    have hcS : c ∈ S := ⟨τ, hτ, hc⟩
    have hzp : (⟨c, hcS⟩ : S) ∈ Subgroup.zpowers g := hg ⟨c, hcS⟩
    rw [Subgroup.mem_zpowers_iff] at hzp
    obtain ⟨z, hz⟩ := hzp
    have hzF : c₀ ^ z = c := by
      have := congrArg (fun s : S => (s : F)) hz
      simpa using this

    set k : ℕ := (z % (n : ℤ)).toNat with hk
    have hmod_nonneg : 0 ≤ z % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn0.ne')
    have hmod_lt : z % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hn0)
    have hkz : ((k : ℕ) : ℤ) = z % (n : ℤ) := by rw [hk, Int.toNat_of_nonneg hmod_nonneg]
    have hkn : k < n := by
      have : ((k : ℕ) : ℤ) < (n : ℤ) := hkz ▸ hmod_lt
      exact_mod_cast this
    have hck : c₀ ^ k = c := by
      rw [← hzF, ← zpow_natCast, hkz, hn, zpow_mod_orderOf]
    refine ⟨k, hkn, ?_⟩

    have hA' := hpw hτ₀ hR₀ (n - k)
    have hprod : Adm (τ₀ ^ (n - k) * τ) := hmul _ _ hA'.1 hτ
    have hRprod : R (τ₀ ^ (n - k) * τ) 1 := by
      have := hRmul _ _ _ _ hA'.1 hτ hA'.2 hc
      rwa [← hck, ← pow_add, Nat.sub_add_cancel hkn.le, hn, pow_orderOf_eq_one] at this
    have h1' : τ₀ ^ (n - k) * τ = 1 := hfaith _ hprod hRprod
    have h2' : τ₀ ^ (n - k) * τ₀ ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hkn.le, hτ₀n]
    exact mul_left_cancel (h1'.trans h2'.symm)

end Core

section Drinfeld

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]

theorem hAction_x_of_fst_eq_one (p : ↥(DrinfeldCurve.hSubgroup q)) (c : (GaloisField q 2)ˣ)
    (hp : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) = (1, c)) :
    DrinfeldCurve.hAction q k p (DrinfeldCurve.x q k) =
      algebraMap k (DrinfeldCurve.CoordRing q k) (algebraMap (GaloisField q 2) k c) * DrinfeldCurve.x q k := by
  have h1 : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 = 1 := by rw [hp]
  have h2 : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 = c := by rw [hp]
  show DrinfeldCurve.hAction q k p (DrinfeldCurve.mk q k (MvPolynomial.X 0)) = _
  rw [DrinfeldCurve.hAction_mk, h1, h2]
  have hone : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 := rfl
  rw [hone, DrinfeldCurve.substPoly_one, AlgHom.id_apply, DrinfeldCurve.scalePoly_X, map_mul,
    ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rfl

theorem units_eq_of_forall_hAction_eq [Nontrivial (DrinfeldCurve.CoordRing q k)]
    (p p' : ↥(DrinfeldCurve.hSubgroup q)) (c c' : (GaloisField q 2)ˣ)
    (hp : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) = (1, c))
    (hp' : (p' : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) = (1, c'))
    (h : ∀ z, DrinfeldCurve.hAction q k p z = DrinfeldCurve.hAction q k p' z) : c = c' := by
  by_contra hcc
  have hx := h (DrinfeldCurve.x q k)
  rw [hAction_x_of_fst_eq_one q k p c hp, hAction_x_of_fst_eq_one q k p' c' hp'] at hx
  set d : k := algebraMap (GaloisField q 2) k c - algebraMap (GaloisField q 2) k c' with hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hcc
    have : (algebraMap (GaloisField q 2) k) c = (algebraMap (GaloisField q 2) k) c' := sub_eq_zero.mp h0
    exact Units.ext ((algebraMap (GaloisField q 2) k).injective this)
  have hdx : algebraMap k (DrinfeldCurve.CoordRing q k) d * DrinfeldCurve.x q k = 0 := by
    rw [hd, map_sub, sub_mul, hx, sub_self]
  have hx0 : DrinfeldCurve.x q k = 0 := by
    have := congrArg (fun t => algebraMap k (DrinfeldCurve.CoordRing q k) d⁻¹ * t) hdx
    simpa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0] using this
  have hrel := DrinfeldCurve.relation q k
  rw [hx0, zero_mul, zero_pow (Fact.out : q.Prime).ne_zero, zero_mul, sub_zero] at hrel
  exact zero_ne_one hrel

theorem pow_eq_one_of_fst_eq_one (p : ↥(DrinfeldCurve.hSubgroup q)) (c : (GaloisField q 2)ˣ)
    (hp : (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) = (1, c)) :
    c ^ (q + 1) = 1 := by
  have hmem := (DrinfeldCurve.mem_hSubgroup_iff q _).mp p.2
  have h2 := congrArg (fun u : (GaloisField q 2)ˣ => (u : GaloisField q 2)) hmem
  simp only [DrinfeldCurve.coe_hChar_apply, hp, Units.val_one] at h2
  simp only [Matrix.det_one, map_one, one_mul] at h2
  ext
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one]

end Drinfeld

end EndsCyclicLinkedSol

open EndsCyclicLinkedSol in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
                (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W)) :

      (∃ (n : ℕ) (_ : 1 ≤ n) (_ : n ∣ q + 1) (γ₀ : SL(2, ℤ)) (_ : γ₀ ∈ CongruenceSubgroup.Gamma q) (_ : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
          (τ₀ : ↥K ≃ₐ[L] ↥K) (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ₀⁻¹ K τ₀) (_ : ∀ f : ↥K, f ∈ W ↔ τ₀ f ∈ W),
        (∀ f : ↥K, f ∈ B → (τ₀ ^ n) f = f) ∧
        (∀ k : ℕ, 0 < k → k < n → ∃ f : ↥K, f ∈ B ∧ (τ₀ ^ k) f ≠ f) ∧
        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) → ∃ k : ℕ, k < n ∧ ∀ f : ↥K, f ∈ B → τ f = (τ₀ ^ k) f)) := by
  classical

  haveI hcharP : CharP (ResidueField A) q := by
    have h0 : ((q : ℕ) : ResidueField A) = 0 := by
      have : ((q : ℕ) : ResidueField A) = IsLocalRing.residue A (q : A) := by simp
      rw [this, IsLocalRing.residue_eq_zero_iff]
      exact hAq
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr h0
  letI algZ : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
  letI inst : Algebra (GaloisField q 2) (ResidueField A) :=
    ((IsAlgClosed.lift : GaloisField q 2 →ₐ[ZMod q] ResidueField A).toRingHom).toAlgebra

  obtain ⟨ρ, hρsurj, hρker, -, hρeq⟩ := hEQ.1 inst
  have hBstab := hEQ.2.1
  obtain ⟨-, hcomp, hone⟩ :=
    ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ
      hι K hK

  haveI hnt : Nontrivial (DrinfeldCurve.CoordRing q (ResidueField A)) := by
    by_contra htriv
    rw [not_nontrivial_iff_subsingleton] at htriv
    have h10 : ρ 1 = 0 := Subsingleton.elim _ _
    have hmem := (hρker 1).mp h10
    apply (IsLocalRing.maximalIdeal.isMaximal (↥W)).ne_top
    rw [Ideal.eq_top_iff_one]
    have h1W : (1 : ↥W) = ⟨((1 : ↥B) : ↥K), hBW _ (1 : ↥B).2⟩ := Subtype.ext rfl
    rw [h1W]
    exact hmem

  let Adm : (↥K ≃ₐ[L] ↥K) → Prop := fun τ =>
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')
        γ⁻¹ K τ ∧ (∀ f : ↥K, f ∈ W ↔ τ f ∈ W)
  let R : (↥K ≃ₐ[L] ↥K) → (GaloisField q 2)ˣ → Prop := fun τ c =>
    ∃ p : ↥(DrinfeldCurve.hSubgroup q),
      (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ) = (1, c) ∧
      ∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) p (ρ b)

  have hAdmB : ∀ τ, Adm τ → ∀ f : ↥K, f ∈ B → τ f ∈ B := by
    rintro τ ⟨γ, -, hγM, hτ, -⟩ f hf
    exact hBstab γ hγM τ hτ f hf
  have h1 : Adm 1 := by
    refine ⟨1, one_mem _, one_mem _, ?_, fun f => Iff.rfl⟩
    rw [inv_one]
    exact hone 1 (one_mem _) (one_mem _)
  have hR1 : R 1 1 := by
    refine ⟨1, rfl, fun b hb => ?_⟩
    rw [map_one]
    exact congrArg ρ (Subtype.ext rfl)
  have hmul : ∀ τ τ', Adm τ → Adm τ' → Adm (τ * τ') := by
    rintro τ τ' ⟨γ, hγq, hγM, hτ, hW⟩ ⟨γ', hγq', hγM', hτ', hW'⟩
    refine ⟨γ * γ', mul_mem hγq hγq', mul_mem hγM hγM', ?_, fun f => ?_⟩
    · rw [mul_inv_rev]
      exact hcomp γ⁻¹ γ'⁻¹ (inv_mem hγM) (inv_mem hγM') τ τ' hτ hτ'
    · rw [AlgEquiv.mul_apply]
      exact (hW' f).trans (hW _)
  have hRmul : ∀ τ τ' c c', Adm τ → Adm τ' → R τ c → R τ' c' → R (τ * τ') (c * c') := by
    rintro τ τ' c c' hτ hτ' ⟨p, hp, hpe⟩ ⟨p', hp', hpe'⟩
    refine ⟨p * p', by rw [Subgroup.coe_mul, hp, hp', Prod.mk_mul_mk, one_mul], fun b hb => ?_⟩
    have hb' : τ' (b : ↥K) ∈ B := hAdmB τ' hτ' _ b.2
    have := hpe ⟨τ' (b : ↥K), hb'⟩ hb
    rw [map_mul]
    show ρ ⟨τ (τ' (b : ↥K)), hb⟩ =
      DrinfeldCurve.hAction q (ResidueField A) p (DrinfeldCurve.hAction q (ResidueField A) p' (ρ b))
    rw [← hpe' b hb']
    exact this
  have hredQ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → ModularCurve.FullLevel.redQ q γ = 1 := by
    intro γ hγ
    have h := CongruenceSubgroup.Gamma_mem'.mp hγ
    show Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) = 1
    rw [h, map_one]
  have hex : ∀ τ, Adm τ → ∃ c, R τ c ∧ (τ ≠ 1 → c ≠ 1) := by
    rintro τ ⟨γ, hγq, hγM, hτ, hW⟩
    obtain ⟨c, hmem, hact, hfaith⟩ := hρeq γ hγM τ hτ hW
    refine ⟨c, ⟨⟨_, hmem⟩, ?_, hact⟩, fun hne => hfaith hγq fun hall => hne (AlgEquiv.ext hall)⟩
    show (ModularCurve.FullLevel.redQ q γ, c) = (1, c)
    rw [hredQ γ hγq]
  have huniq : ∀ τ c c', Adm τ → R τ c → R τ c' → c = c' := by
    rintro τ c c' hτ ⟨p, hp, hpe⟩ ⟨p', hp', hpe'⟩
    refine units_eq_of_forall_hAction_eq q (ResidueField A) p p' c c' hp hp' fun z => ?_
    obtain ⟨b, rfl⟩ := hρsurj z
    have hb : τ (b : ↥K) ∈ B := hAdmB τ hτ _ b.2
    rw [← hpe b hb, ← hpe' b hb]
  have hpow : ∀ τ c, Adm τ → R τ c → c ^ (q + 1) = 1 := by
    rintro τ c - ⟨p, hp, -⟩
    exact pow_eq_one_of_fst_eq_one q p c hp

  obtain ⟨n, τ₀, c₀, hn0, hndvd, ⟨γ₀, hγ₀q, hγ₀M, hτ₀, hW₀⟩, hR₀, hτ₀n, hexact, hall⟩ :=
    exists_generator_of_faithful_scalar (G := (↥K ≃ₐ[L] ↥K)) (F := (GaloisField q 2)ˣ) Adm R (q + 1)
      h1 hR1 hmul hRmul hex huniq hpow
  refine ⟨n, hn0, hndvd, γ₀, hγ₀q, hγ₀M, τ₀, hτ₀, hW₀, ?_, ?_, ?_⟩
  ·
    intro f _
    rw [hτ₀n, AlgEquiv.one_apply]
  ·
    intro k hk hkn
    by_contra hcon
    push Not at hcon
    apply hexact k hk hkn
    refine ⟨1, rfl, fun b hb => ?_⟩
    rw [map_one, AlgEquiv.one_apply]
    congr 1
    exact Subtype.ext (hcon (b : ↥K) b.2)
  ·
    intro γ hγq hγM τ hτ hW
    obtain ⟨k, hkn, rfl⟩ := hall τ ⟨γ, hγq, hγM, hτ, hW⟩
    exact ⟨k, hkn, fun f _ => rfl⟩

end S_ModularCurve_FullLevel_AuxLevel_exists_levelAut_pow_eq_and_forall_eq_pow_blowupChart_of_eq_adjoin_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_levelAut_pow_eq_and_forall_eq_pow_blowupChart_of_eq_adjoin_of_drinfeldChartWitness_linked (solution)
