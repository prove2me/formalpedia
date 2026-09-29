-- Prove2me | solution 1 for ModularCurve.pair_normFreeEnd_eq_pair_normFreeEnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9371d446-76fb-5333-bc28-8f8ca3dfba7a

import Mathlib
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_ModularCurve_diamondOneBar_mul_of_coprime
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pair_normFreeEnd_eq_pair_normFreeEnd
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Ws23InjA

open AlgebraicCurve

section Abstract

variable {K F : Type} [Field K] [Field F] [Algebra K F] {n : ℕ}

theorem sum_inv_smul_eq_sum_smul {ι : Type} [DecidableEq ι] (S : Finset ι) (G : ι → SemilinearAut K F)
    (inv : ι → ι) (hmaps : ∀ i ∈ S, inv i ∈ S) (hinj : Set.InjOn inv S)
    (hG : ∀ i ∈ S, ∀ t : Pic0.torsion K F n, (G i)⁻¹ • t = G (inv i) • t) (t : Pic0.torsion K F n) :
    ∑ i ∈ S, (G i)⁻¹ • t = ∑ i ∈ S, G i • t := by
  rw [Finset.sum_congr rfl fun i hi => hG i hi t]
  exact Finset.sum_nbij inv hmaps hinj
    (Finset.surjOn_of_injOn_of_card_le _ hmaps hinj le_rfl) (fun _ _ => rfl)

def prU (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (a b : Pic0.torsion K F n) : Kˣ :=
  Units.mk0 (pr a b) (hne a b)

theorem val_prU (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (a b : Pic0.torsion K F n) : (prU pr hne a b : K) = pr a b := rfl

def prL (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (haddL : ∀ a a' b, pr (a + a') b = pr a b * pr a' b) (b : Pic0.torsion K F n) :
    Pic0.torsion K F n →+ Additive Kˣ :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (prU pr hne a b)) fun a a' =>
    congrArg Additive.ofMul (Units.ext (by
      simp only [prU, Units.val_mk0, Units.val_mul]
      exact haddL a a' b))

def prR (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (haddR : ∀ a b b', pr a (b + b') = pr a b * pr a b') (a : Pic0.torsion K F n) :
    Pic0.torsion K F n →+ Additive Kˣ :=
  AddMonoidHom.mk' (fun b => Additive.ofMul (prU pr hne a b)) fun b b' =>
    congrArg Additive.ofMul (Units.ext (by
      simp only [prU, Units.val_mk0, Units.val_mul]
      exact haddR a b b'))

theorem prL_apply (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (haddL : ∀ a a' b, pr (a + a') b = pr a b * pr a' b) (b a : Pic0.torsion K F n) :
    prL pr hne haddL b a = Additive.ofMul (prU pr hne a b) := rfl

theorem prR_apply (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (haddR : ∀ a b b', pr a (b + b') = pr a b * pr a b') (a b : Pic0.torsion K F n) :
    prR pr hne haddR a b = Additive.ofMul (prU pr hne a b) := rfl

theorem key (pr : Pic0.torsion K F n → Pic0.torsion K F n → K) (hne : ∀ a b, pr a b ≠ 0)
    (haddL : ∀ a a' b, pr (a + a') b = pr a b * pr a' b)
    (haddR : ∀ a b b', pr a (b + b') = pr a b * pr a b')
    {ι : Type} (S : Finset ι) (G : ι → SemilinearAut K F)
    (hinvar : ∀ i ∈ S, ∀ a b : Pic0.torsion K F n, pr (G i • a) (G i • b) = pr a b)
    (hclosed : ∀ b : Pic0.torsion K F n, ∑ i ∈ S, (G i)⁻¹ • b = ∑ i ∈ S, G i • b)
    (m : ℕ) (a b : Pic0.torsion K F n) :
    pr (m • a - ∑ i ∈ S, G i • a) b = pr a (m • b - ∑ i ∈ S, G i • b) := by

  have hadj : ∀ i ∈ S, ∀ a b : Pic0.torsion K F n, pr (G i • a) b = pr a ((G i)⁻¹ • b) := by
    intro i hi a b
    conv_lhs => rw [← smul_inv_smul (G i) b]
    exact hinvar i hi a _

  have h1 : ∀ a' b' : Pic0.torsion K F n, prL pr hne haddL b' a' = prR pr hne haddR a' b' := fun _ _ => rfl
  have h2 : ∑ i ∈ S, prL pr hne haddL b (G i • a) = ∑ i ∈ S, prR pr hne haddR a (G i • b) := by
    calc ∑ i ∈ S, prL pr hne haddL b (G i • a)
        = ∑ i ∈ S, prR pr hne haddR a ((G i)⁻¹ • b) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [prL_apply, prR_apply]
          exact congrArg Additive.ofMul (Units.ext (hadj i hi a b))
      _ = prR pr hne haddR a (∑ i ∈ S, (G i)⁻¹ • b) := by rw [map_sum]
      _ = prR pr hne haddR a (∑ i ∈ S, G i • b) := by rw [hclosed b]
      _ = ∑ i ∈ S, prR pr hne haddR a (G i • b) := by rw [map_sum]
  have h : prL pr hne haddL b (m • a - ∑ i ∈ S, G i • a) = prR pr hne haddR a (m • b - ∑ i ∈ S, G i • b) := by
    rw [map_sub, map_sub, map_nsmul, map_nsmul, map_sum, map_sum, h1, h2]
  have h' := congrArg (fun u : Additive Kˣ => ((Additive.toMul u : Kˣ) : K)) h
  simp only [prL_apply, prR_apply, toMul_ofMul, val_prU] at h'
  exact h'

end Abstract

end Ws23InjA

namespace Ws23InjA

open AlgebraicCurve ModularCurve Finset

section Modular

variable (M : ℕ)

theorem isDiamondAut_eq_of_modEq {d e : ℕ} (h : d ≡ e [MOD M]) :
    IsDiamondAut M d = IsDiamondAut M e := by
  funext σ
  have hc : Nat.Coprime d M ↔ Nat.Coprime e M := by
    unfold Nat.Coprime; rw [h.gcd_eq]
  have hz : (d : ZMod M) = (e : ZMod M) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simp only [IsDiamondAut, hz, hc]

theorem diamondAut_eq_of_modEq {d e : ℕ} (h : d ≡ e [MOD M]) : diamondAut M d = diamondAut M e := by
  have key : ∀ (P Q : (x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) → Prop), P = Q →
      (haveI := Classical.dec (∃ σ, P σ); if hP : ∃ σ, P σ then hP.choose else AlgEquiv.refl) =
      (haveI := Classical.dec (∃ σ, Q σ); if hQ : ∃ σ, Q σ then hQ.choose else AlgEquiv.refl) := by
    rintro P Q rfl; rfl
  exact key _ _ (isDiamondAut_eq_of_modEq M h)

theorem diamondOneBar_eq_of_modEq {d e : ℕ} (h : d ≡ e [MOD M]) : diamondOneBar M d = diamondOneBar M e := by
  have : diamondAutBar M d = diamondAutBar M e := by
    unfold diamondAutBar; rw [diamondAut_eq_of_modEq M h]
  apply LinearMap.ext; intro x
  rw [diamondOneBar_apply, diamondOneBar_apply, this]

variable [NeZero M]

def G (d : ℕ) : SemilinearAut (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) :=
  SemilinearAut.ofAlgAut (diamondAutBar M d)

theorem diamondOneBar_eq_smul (d : ℕ) (z : JOne M) : diamondOneBar M d z = G M d • z := rfl

theorem smul_smul_eq (d d' : ℕ) (hd : Nat.Coprime d M) (hd' : Nat.Coprime d' M) (z : JOne M) :
    G M d • (G M d' • z) = diamondOneBar M (d * d') z := by
  rw [ModularCurve.diamondOneBar_mul_of_coprime M (ModularCurve.heckeDiamondInputsAll M).2 d d' hd hd']
  rfl

theorem one_smul_G (z : JOne M) : G M 1 • z = z := by
  have h := smul_smul_eq M 1 1 (Nat.coprime_one_left M) (Nat.coprime_one_left M) z
  rw [mul_one, diamondOneBar_eq_smul] at h
  exact MulAction.injective (G M 1) h

theorem smul_smul_eq_self_of_modEq_one {d d' : ℕ} (hd : Nat.Coprime d M) (hd' : Nat.Coprime d' M)
    (h1 : d * d' ≡ 1 [MOD M]) (z : JOne M) : G M d • (G M d' • z) = z := by
  rw [smul_smul_eq M d d' hd hd', diamondOneBar_eq_of_modEq M h1, diamondOneBar_eq_smul, one_smul_G]

theorem inv_smul_torsion_eq {n : ℕ} {d d' : ℕ} (hd : Nat.Coprime d M) (hd' : Nat.Coprime d' M)
    (h1 : d * d' ≡ 1 [MOD M]) (t : Pic0.torsion (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) n) :
    (G M d)⁻¹ • t = G M d' • t := by
  symm
  rw [eq_inv_smul_iff]
  exact Subtype.ext (by
    rw [SemilinearAut.coe_torsion_smul, SemilinearAut.coe_torsion_smul]
    exact smul_smul_eq_self_of_modEq_one M hd hd' h1 _)

variable (q : ℕ)

theorem mul_mod_mem (hqM : q ∣ M) (hM : 0 < M) {d d' : ℕ} (hd : d ∈ normFreeRepsAt M q)
    (hd' : d' ∈ normFreeRepsAt M q) : (d * d') % M ∈ normFreeRepsAt M q := by
  rw [mem_normFreeRepsAt] at hd hd' ⊢
  refine ⟨Nat.mod_lt _ hM, ?_, ?_⟩
  · have h1 : Nat.Coprime (d * d') M := Nat.Coprime.mul_left hd.2.1 hd'.2.1
    unfold Nat.Coprime at h1 ⊢
    rw [← h1]; exact (Nat.mod_modEq _ _).gcd_eq
  · have hdvd : M / q ∣ M := Nat.div_dvd_of_dvd hqM
    have h2 : d * d' ≡ 1 [MOD M / q] := by simpa using Nat.ModEq.mul hd.2.2 hd'.2.2
    exact ((Nat.mod_modEq (d * d') M).of_dvd hdvd).trans h2

theorem mul_mod_injOn (hM : 0 < M) {d : ℕ} (hd : d ∈ normFreeRepsAt M q) :
    Set.InjOn (fun d' => (d * d') % M) (normFreeRepsAt M q : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, mem_normFreeRepsAt] at ha hb
  rw [mem_normFreeRepsAt] at hd
  have h1 : d * a ≡ d * b [MOD M] := hab
  have h2 : a ≡ b [MOD M] := Nat.ModEq.cancel_left_of_coprime (by
    have := hd.2.1; unfold Nat.Coprime at this; rwa [Nat.gcd_comm]) h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 ha.1 hb.1

theorem one_mod_mem (hqM : q ∣ M) (hM : 0 < M) : 1 % M ∈ normFreeRepsAt M q := by
  rw [mem_normFreeRepsAt]
  refine ⟨Nat.mod_lt _ hM, ?_, ?_⟩
  · unfold Nat.Coprime
    rw [(Nat.mod_modEq 1 M).gcd_eq]
    exact Nat.gcd_one_left M
  · exact (Nat.mod_modEq 1 M).of_dvd (Nat.div_dvd_of_dvd hqM)

theorem exists_inv (hqM : q ∣ M) (hM : 0 < M) {d : ℕ} (hd : d ∈ normFreeRepsAt M q) :
    ∃ d' ∈ normFreeRepsAt M q, d * d' ≡ 1 [MOD M] := by
  have hsurj := Finset.surjOn_of_injOn_of_card_le (fun d' => (d * d') % M)
    (fun d' hd' => mul_mod_mem M q hqM hM hd hd') (mul_mod_injOn M q hM hd) le_rfl
  obtain ⟨d', hd', h⟩ := hsurj (Finset.mem_coe.mpr (one_mod_mem M q hqM hM))
  exact ⟨d', hd', h⟩

noncomputable def invRep (hqM : q ∣ M) (hM : 0 < M) (d : ℕ) : ℕ :=
  if hd : d ∈ normFreeRepsAt M q then (exists_inv M q hqM hM hd).choose else d

theorem invRep_mem (hqM : q ∣ M) (hM : 0 < M) {d : ℕ} (hd : d ∈ normFreeRepsAt M q) :
    invRep M q hqM hM d ∈ normFreeRepsAt M q := by
  rw [invRep, dif_pos hd]; exact (exists_inv M q hqM hM hd).choose_spec.1

theorem mul_invRep_modEq (hqM : q ∣ M) (hM : 0 < M) {d : ℕ} (hd : d ∈ normFreeRepsAt M q) :
    d * invRep M q hqM hM d ≡ 1 [MOD M] := by
  rw [invRep, dif_pos hd]; exact (exists_inv M q hqM hM hd).choose_spec.2

theorem invRep_injOn (hqM : q ∣ M) (hM : 0 < M) :
    Set.InjOn (invRep M q hqM hM) (normFreeRepsAt M q : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  have hca := mul_invRep_modEq M q hqM hM ha
  have hcb := mul_invRep_modEq M q hqM hM hb
  rw [hab] at hca
  set c := invRep M q hqM hM b
  have hc : c ∈ normFreeRepsAt M q := invRep_mem M q hqM hM hb
  rw [mem_normFreeRepsAt] at ha hb hc
  have h1 : a * c ≡ b * c [MOD M] := hca.trans hcb.symm
  have h2 : a ≡ b [MOD M] := Nat.ModEq.cancel_right_of_coprime (by
    have := hc.2.1; unfold Nat.Coprime at this; rwa [Nat.gcd_comm]) h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 ha.1 hb.1

theorem sum_inv_smul_eq (hqM : q ∣ M) {n : ℕ}
    (t : Pic0.torsion (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) n) :
    ∑ d ∈ normFreeRepsAt M q, (G M d)⁻¹ • t = ∑ d ∈ normFreeRepsAt M q, G M d • t := by
  classical
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  refine sum_inv_smul_eq_sum_smul (normFreeRepsAt M q) (G M) (invRep M q hqM hM)
    (fun d hd => invRep_mem M q hqM hM hd) (invRep_injOn M q hqM hM) (fun d hd t => ?_) t
  have hd' := invRep_mem M q hqM hM hd
  exact inv_smul_torsion_eq M (mem_normFreeRepsAt.mp hd).2.1 (mem_normFreeRepsAt.mp hd').2.1
    (mul_invRep_modEq M q hqM hM hd) t

theorem normFreeEnd_torsion_eq (S : Finset ℕ) {n : ℕ} (x : JOne M) (hx : (n : ℤ) • x = 0)
    (hNx : (n : ℤ) • normFreeEnd M S x = 0) :
    (⟨normFreeEnd M S x, Pic0.mem_torsion.mpr hNx⟩ :
        Pic0.torsion (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) n) =
      S.card • (⟨x, Pic0.mem_torsion.mpr hx⟩ : Pic0.torsion (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) n) -
        ∑ d ∈ S, G M d • (⟨x, Pic0.mem_torsion.mpr hx⟩ :
          Pic0.torsion (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) n) := by
  apply Subtype.ext
  rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_nsmul, AddSubmonoidClass.coe_finset_sum]
  simp only [SemilinearAut.coe_torsion_smul, normFreeEnd_apply, diamondOneBar_eq_smul]

end Modular

end Ws23InjA

namespace Ws23InjA

open AlgebraicCurve ModularCurve

theorem main
    (M q : ℕ) [NeZero M] (hqM : q ∣ M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    {n : ℕ} [NeZero n]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) n)
    (x y : ModularCurve.JOne M) (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0)
    (hNx : (n : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) x = 0)
    (hNy : (n : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) y = 0) :
    e.pair ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) x, AlgebraicCurve.Pic0.mem_torsion.mpr hNx⟩
        ⟨y, AlgebraicCurve.Pic0.mem_torsion.mpr hy⟩ =
      e.pair ⟨x, AlgebraicCurve.Pic0.mem_torsion.mpr hx⟩
        ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) y, AlgebraicCurve.Pic0.mem_torsion.mpr hNy⟩ := by
  classical
  rw [normFreeEnd_torsion_eq M _ x hx hNx, normFreeEnd_torsion_eq M _ y hy hNy]
  refine key e.pair e.pair_ne_zero e.pair_add_left e.pair_add_right (normFreeRepsAt M q) (G M)
    (fun d _ a b => ?_) (fun b => sum_inv_smul_eq M q hqM b) _ _ _
  rw [G, AlgebraicCurve.DivisorialWeilPairingData.pair_semilinearSmul, SemilinearAut.baseAut_ofAlgAut]
  rfl

end Ws23InjA

theorem solution
    (M q : ℕ) [NeZero M] (hqM : q ∣ M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    {n : ℕ} [NeZero n]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) n)
    (x y : ModularCurve.JOne M) (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0)
    (hNx : (n : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) x = 0)
    (hNy : (n : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) y = 0) :
    e.pair ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) x, AlgebraicCurve.Pic0.mem_torsion.mpr hNx⟩
        ⟨y, AlgebraicCurve.Pic0.mem_torsion.mpr hy⟩ =
      e.pair ⟨x, AlgebraicCurve.Pic0.mem_torsion.mpr hx⟩
        ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) y, AlgebraicCurve.Pic0.mem_torsion.mpr hNy⟩ :=
  Ws23InjA.main M q hqM e x y hx hy hNx hNy

end

end S_ModularCurve_pair_normFreeEnd_eq_pair_normFreeEnd
end P2MW
export P2MW.S_ModularCurve_pair_normFreeEnd_eq_pair_normFreeEnd (solution)
