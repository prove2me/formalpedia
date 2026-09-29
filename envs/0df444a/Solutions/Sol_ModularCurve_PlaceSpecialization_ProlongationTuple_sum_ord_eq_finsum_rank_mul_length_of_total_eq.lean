-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d903e6be-c00c-5e35-927c-5d2c6ce0acd1

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_le_finsum_rank_mul_length_of_ringEquiv_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_of_total_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace NodeDepthCount

open IsLocalRing

theorem algebraMap_adicCompletion_injective (B : Type*) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] :
    Function.Injective (algebraMap B (AdicCompletion (maximalIdeal B) B)) := by
  haveI : IsHausdorff (maximalIdeal B) B := by
    rw [isHausdorff_iff]
    intro x hx
    have hmem : ∀ n : ℕ, x ∈ (maximalIdeal B) ^ n := fun n => by
      have h := hx n
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h
      exact h
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
    have hx' : x ∈ (⨅ n : ℕ, (maximalIdeal B) ^ n) := Ideal.mem_iInf.mpr hmem
    rwa [hbot, Ideal.mem_bot] at hx'
  intro x y hxy
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at hxy
  exact AdicCompletion.of_injective _ _ hxy

end NodeDepthCount

namespace NodeDepthCount

open IsLocalRing in

theorem ringEquiv_algebraMap_adicCompletion_ne_zero {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    {S : Type*} [NonAssocSemiring S] (ι : AdicCompletion (maximalIdeal B) B ≃+* S) (f : B) (hf : f ≠ 0) :
    ι (algebraMap B (AdicCompletion (maximalIdeal B) B) f) ≠ 0 := by
  intro h0
  apply hf
  have hA : algebraMap B (AdicCompletion (maximalIdeal B) B) f = 0 :=
    ι.injective (by rw [h0, map_zero])
  exact algebraMap_adicCompletion_injective B (by rw [hA, map_zero])

end NodeDepthCount

namespace NodeDepthCount

theorem natCast_mul_eq_natCast_mul_iff {k : ℕ} (hk : k ≠ 0) (b c : ℕ∞) :
    (k : ℕ∞) * b = (k : ℕ∞) * c ↔ b = c := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hk' : (k : ℕ∞) ≠ 0 := by exact_mod_cast hk
  induction b using ENat.recTopCoe with
  | top =>
    induction c using ENat.recTopCoe with
    | top => rfl
    | coe c =>
      exfalso
      rw [ENat.mul_top hk'] at h
      exact (ENat.coe_ne_top (k * c)) (by push_cast; exact h.symm)
  | coe b =>
    induction c using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top hk'] at h
      exact (ENat.coe_ne_top (k * b)) (by push_cast; exact h)
    | coe c =>
      have h' : ((k * b : ℕ) : ℕ∞) = ((k * c : ℕ) : ℕ∞) := by push_cast; exact h
      have h'' : k * b = k * c := by exact_mod_cast h'
      exact congrArg _ (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h'')

theorem pow_eq_pow_iff_of_ne_zero' {G : Type*} [LinearOrderedCommGroupWithZero G] {n : ℕ} (hn : n ≠ 0)
    (a b : G) : a ^ n = b ^ n ↔ a = b :=
  pow_left_inj₀ zero_le' zero_le' hn

theorem scale_aux {E r' p' R : ℕ} (hp' : 1 ≤ p') (hpE : p' + 1 ≤ r' * E) (hdvd : r' ∣ R)
    (hR : 1 ≤ R) :
    1 ≤ p' * (R / r') ∧ p' * (R / r') + 1 ≤ R * E ∧ R = r' * (R / r') := by
  obtain ⟨k, rfl⟩ := hdvd
  have hr' : 0 < r' := Nat.pos_of_ne_zero (by rintro rfl; simp at hR)
  have hk : r' * k / r' = k := Nat.mul_div_cancel_left k hr'
  rw [hk]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hR)
  have hmul : (p' + 1) * k ≤ r' * E * k := Nat.mul_le_mul_right k hpE
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, rfl⟩
  nlinarith [hmul, hk1]

theorem mem_of_length_localizedModule_quotient_ne_zero {S : Type*} [CommRing S] (x : S) (Q : PrimeSpectrum S)
    (h : Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl (S ⧸ Ideal.span {x})) ≠ 0) :
    x ∈ Q.asIdeal := by
  by_contra hx
  apply h
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  intro m
  refine ⟨x, hx, ?_⟩
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)

open Finset in

theorem sum_eq_finsum_of_forall_le_of_total_eq
    {Pl Pr G : Type*} [LinearOrderedCommGroupWithZero G] (E : ℕ)
    (o₁ o₂ : Pl → Prop) (Ttot : Finset Pl) (hTtot : ∀ V, V ∈ Ttot ↔ o₁ V ∧ o₂ V)
    (ordZ : Pl → ℤ) (xd : Pl → G) (vϖ : G)
    (hdepV : ∀ V, o₂ V → ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧ xd V ^ r = vϖ ^ p)
    (h₁ h₂ memx : Pr → Prop) (rk : Pr → ℕ) (lenU mult : Pr → ℕ∞)
    (hdepQ : ∀ Q, h₁ Q → h₂ Q → 1 ≤ rk Q ∧ lenU Q ≠ ⊤ ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞))
    (hmult : ∀ Q, mult Q ≠ 0 → memx Q)
    (hfin : {Q : Pr | h₁ Q ∧ h₂ Q ∧ memx Q}.Finite)
    (hLE : ∀ (r : ℕ), 1 ≤ r → ∀ (p : ℕ), 1 ≤ p → p + 1 ≤ r * E → ∀ T : Finset Pl,
      (∀ V, V ∈ T ↔ o₁ V ∧ o₂ V ∧ xd V ^ r = vϖ ^ p) →
      ((∑ V ∈ T, (ordZ V).toNat : ℕ) : ℕ∞) ≤
        ∑ᶠ (Q : Pr) (_ : h₁ Q ∧ h₂ Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q)
    (htot : ((∑ V ∈ Ttot, (ordZ V).toNat : ℕ) : ℕ∞) = ∑ᶠ (Q : Pr) (_ : h₁ Q ∧ h₂ Q), (rk Q : ℕ∞) * mult Q)
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ) (hp1 : 1 ≤ p) (hpE : p + 1 ≤ r * E)
    (T : Finset Pl) (hT : ∀ V, V ∈ T ↔ o₁ V ∧ o₂ V ∧ xd V ^ r = vϖ ^ p) :
    ((∑ V ∈ T, (ordZ V).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : Pr) (_ : h₁ Q ∧ h₂ Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q := by
  classical

  set horiz : Pr → Prop := fun Q => h₁ Q ∧ h₂ Q with hhoriz
  have hfin' : {Q : Pr | horiz Q ∧ mult Q ≠ 0}.Finite :=
    hfin.subset fun Q hQ => ⟨hQ.1.1, hQ.1.2, hmult Q hQ.2⟩

  have hdepV' : ∀ V ∈ Ttot, ∃ r' p' : ℕ, 1 ≤ r' ∧ 1 ≤ p' ∧ p' + 1 ≤ r' * E ∧ xd V ^ r' = vϖ ^ p' := by
    intro V hV
    obtain ⟨r', hr', p', hp', hpE', hx⟩ := hdepV V ((hTtot V).mp hV).2
    exact ⟨r', p', hr', hp', hpE', hx⟩
  choose! rV pV hrV hpV hpVE hxV using hdepV'
  have hdepQ' : ∀ Q ∈ hfin'.toFinset, ∃ r' p' : ℕ, 1 ≤ r' ∧ 1 ≤ p' ∧ p' + 1 ≤ r' * E ∧
      (r' : ℕ∞) * lenU Q = ((p' * rk Q : ℕ) : ℕ∞) := by
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    obtain ⟨-, -, r', hr', p', hp', hpE', hx⟩ := hdepQ Q hQ.1.1 hQ.1.2
    exact ⟨r', p', hr', hp', hpE', hx⟩
  choose! rQ pQ hrQ hpQ hpQE hxQ using hdepQ'

  set r₀ : ℕ := (∏ V ∈ Ttot, rV V) * ∏ Q ∈ hfin'.toFinset, rQ Q with hr₀
  have hr₀pos : 1 ≤ r₀ := by
    have h1 : 0 < ∏ V ∈ Ttot, rV V := Finset.prod_pos fun V hV => hrV V hV
    have h2 : 0 < ∏ Q ∈ hfin'.toFinset, rQ Q := Finset.prod_pos fun Q hQ => hrQ Q hQ
    exact Nat.mul_pos h1 h2
  have hr₀ne : r₀ ≠ 0 := by omega
  set R : ℕ := r * r₀ with hR
  have hR1 : 1 ≤ R := Nat.mul_pos hr hr₀pos
  have hRV : ∀ V ∈ Ttot, rV V ∣ R := fun V hV =>
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem rV hV) _) r
  have hRQ : ∀ Q ∈ hfin'.toFinset, rQ Q ∣ R := fun Q hQ =>
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem rQ hQ) _) r
  clear_value r₀ R

  set dep : Pl → ℕ := fun V => pV V * (R / rV V) with hdep_def
  set depQ : Pr → ℕ := fun Q => pQ Q * (R / rQ Q) with hdepQ_def
  have hdep : ∀ V ∈ Ttot, 1 ≤ dep V ∧ dep V + 1 ≤ R * E := fun V hV =>
    let h := scale_aux (hpV V hV) (hpVE V hV) (hRV V hV) hR1
    ⟨h.1, h.2.1⟩
  have hxVR : ∀ V ∈ Ttot, xd V ^ R = vϖ ^ dep V := by
    intro V hV
    have h := (scale_aux (hpV V hV) (hpVE V hV) (hRV V hV) hR1).2.2
    show xd V ^ R = vϖ ^ (pV V * (R / rV V))
    conv_lhs => rw [h]
    rw [pow_mul, hxV V hV, ← pow_mul]
  have hdepQR : ∀ Q, horiz Q → mult Q ≠ 0 →
      1 ≤ depQ Q ∧ depQ Q + 1 ≤ R * E ∧ (R : ℕ∞) * lenU Q = ((depQ Q * rk Q : ℕ) : ℕ∞) ∧
        1 ≤ rk Q ∧ lenU Q ≠ ⊤ := by
    intro Q hQh hQm
    have hQ : Q ∈ hfin'.toFinset := by rw [Set.Finite.mem_toFinset]; exact ⟨hQh, hQm⟩
    obtain ⟨hrk, hlen, -⟩ := hdepQ Q hQh.1 hQh.2
    have h := scale_aux (hpQ Q hQ) (hpQE Q hQ) (hRQ Q hQ) hR1
    refine ⟨h.1, h.2.1, ?_, hrk, hlen⟩
    show (R : ℕ∞) * lenU Q = ((pQ Q * (R / rQ Q) * rk Q : ℕ) : ℕ∞)
    conv_lhs => rw [h.2.2]
    rw [Nat.cast_mul, mul_comm ((rQ Q : ℕ) : ℕ∞), mul_assoc, hxQ Q hQ]
    push_cast
    ring

  obtain ⟨hS, hM⟩ := ENat.sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth E R Ttot ordZ dep hdep
    (fun p' => Ttot.filter fun V => dep V = p') (fun p' V => by rw [Finset.mem_filter])
    horiz rk lenU mult depQ hdepQR hfin'
  set I : Finset ℕ := Finset.Icc 1 (R * E - 1) with hI
  set S' : ℕ → ℕ := fun p' => ∑ V ∈ Ttot.filter (fun V => dep V = p'), (ordZ V).toNat with hS'
  set S'' : ℕ → ℕ := fun p' => ∑ V ∈ Ttot.filter (fun V => xd V ^ R = vϖ ^ p'), (ordZ V).toNat with hS''
  set M' : ℕ → ℕ∞ := fun p' =>
    ∑ᶠ (Q : Pr) (_ : horiz Q ∧ (R : ℕ∞) * lenU Q = ((p' * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q with hM'
  set n : ℕ := ∑ V ∈ Ttot, (ordZ V).toNat with hn
  change (n : ℕ∞) = ∑ p' ∈ I, (S' p' : ℕ∞) at hS
  change (∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q) = ∑ p' ∈ I, M' p' at hM
  change (n : ℕ∞) = ∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q at htot

  have hLE' : ∀ p' ∈ I, (S'' p' : ℕ∞) ≤ M' p' := by
    intro p' hp'
    rw [hI, Finset.mem_Icc] at hp'
    have h := hLE R hR1 p' hp'.1 (by omega) (Ttot.filter (fun V => xd V ^ R = vϖ ^ p'))
      (fun V => by rw [Finset.mem_filter, hTtot, and_assoc])
    refine h.trans_eq (finsum_congr fun Q => finsum_congr_Prop (propext ?_) fun _ => rfl)
    show (h₁ Q ∧ h₂ Q ∧ _) ↔ (horiz Q ∧ _)
    rw [hhoriz, and_assoc]

  have hS'S'' : ∀ p', S' p' ≤ S'' p' := by
    intro p'
    apply Finset.sum_le_sum_of_subset
    intro V
    simp only [Finset.mem_filter]
    rintro ⟨hV, hd⟩
    exact ⟨hV, by rw [hxVR V hV, hd]⟩

  have hMtot : (∑ p' ∈ I, M' p') = (n : ℕ∞) := by rw [← hM, ← htot]
  have hM'ne : ∀ p' ∈ I, M' p' ≠ ⊤ := by
    intro p' hp'
    have hle : M' p' ≤ ∑ p'' ∈ I, M' p'' := Finset.single_le_sum (fun _ _ => zero_le) hp'
    rw [hMtot] at hle
    exact ne_top_of_le_ne_top (ENat.coe_ne_top n) hle
  set m : ℕ → ℕ := fun p' => (M' p').toNat with hm
  have hmM : ∀ p' ∈ I, (m p' : ℕ∞) = M' p' := fun p' hp' => ENat.coe_toNat (hM'ne p' hp')

  have hn1 : n = ∑ p' ∈ I, S' p' := by
    have : (n : ℕ∞) = ((∑ p' ∈ I, S' p' : ℕ) : ℕ∞) := by rw [hS, Nat.cast_sum]
    exact_mod_cast this
  have hn2 : ∑ p' ∈ I, m p' = n := by
    have : ((∑ p' ∈ I, m p' : ℕ) : ℕ∞) = (n : ℕ∞) := by
      rw [← hMtot, Nat.cast_sum]
      exact Finset.sum_congr rfl hmM
    exact_mod_cast this
  have hle1 : ∀ p' ∈ I, S'' p' ≤ m p' := by
    intro p' hp'
    have : (S'' p' : ℕ∞) ≤ (m p' : ℕ∞) := by rw [hmM p' hp']; exact hLE' p' hp'
    exact_mod_cast this
  have hsumeq : ∑ p' ∈ I, S'' p' = ∑ p' ∈ I, m p' := by
    apply le_antisymm (Finset.sum_le_sum hle1)
    rw [hn2, hn1]
    exact Finset.sum_le_sum fun p' _ => hS'S'' p'
  have hterm : ∀ p' ∈ I, S'' p' = m p' := (Finset.sum_eq_sum_iff_of_le hle1).mp hsumeq

  have hpI : p * r₀ ∈ I := by
    rw [hI, Finset.mem_Icc]
    have h1 : 1 ≤ p * r₀ := Nat.mul_pos hp1 hr₀pos
    have h2 : (p + 1) * r₀ ≤ r * E * r₀ := Nat.mul_le_mul_right r₀ hpE
    constructor
    · exact h1
    · have : p * r₀ + 1 ≤ R * E := by rw [hR]; nlinarith [h2, hr₀pos]
      omega
  have hTeq : T = Ttot.filter (fun V => xd V ^ R = vϖ ^ (p * r₀)) := by
    ext V
    have e1 : xd V ^ (r * r₀) = (xd V ^ r) ^ r₀ := pow_mul _ _ _
    have e2 : vϖ ^ (p * r₀) = (vϖ ^ p) ^ r₀ := pow_mul _ _ _
    rw [hT, Finset.mem_filter, hTtot, hR, e1, e2, pow_eq_pow_iff_of_ne_zero' hr₀ne, and_assoc]
  have hcond : ∀ Q, (h₁ Q ∧ h₂ Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)) ↔
      (horiz Q ∧ (R : ℕ∞) * lenU Q = ((p * r₀ * rk Q : ℕ) : ℕ∞)) := by
    intro Q
    rw [hhoriz, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [← natCast_mul_eq_natCast_mul_iff hr₀ne ((r : ℕ∞) * lenU Q), hR]
    constructor
    · intro h
      rw [Nat.cast_mul, mul_comm (r : ℕ∞), mul_assoc, h]
      push_cast; ring
    · intro h
      have e : ((r₀ : ℕ) : ℕ∞) * ((r : ℕ∞) * lenU Q) = ((r * r₀ : ℕ) : ℕ∞) * lenU Q := by push_cast; ring
      rw [e, h]
      push_cast; ring
  calc ((∑ V ∈ T, (ordZ V).toNat : ℕ) : ℕ∞)
      = (S'' (p * r₀) : ℕ∞) := by rw [hTeq]
    _ = (m (p * r₀) : ℕ∞) := by rw [hterm _ hpI]
    _ = M' (p * r₀) := hmM _ hpI
    _ = ∑ᶠ (Q : Pr) (_ : h₁ Q ∧ h₂ Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q :=
        finsum_congr fun Q => finsum_congr_Prop (propext (hcond Q)).symm fun _ => rfl

end NodeDepthCount

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace NodeDepthCount

set_option maxHeartbeats 3200000 in
open ModularCurve.UVCrossingModel in

theorem sum_ord_eq_finsum_rank_mul_length_of_total_eq_frame
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (f : ↥(R.nodeIntegersOver K w)) (hf : f ≠ 0)
    (Ttot : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTtot : ∀ V, V ∈ Ttot ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w))
    (htot : ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})))
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ) (hp1 : 1 ≤ p) (hpE : p + 1 ≤ r * E)
    (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hT : ∀ V, V ∈ T ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w ∧
        c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p)) :
    ((∑ V ∈ T, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (r : ℕ∞) * Module.length W (UVCrossingModel W (π ^ E) ⧸ (Q.asIdeal ⊔ Ideal.span {U (π ^ E)})) =
            ((p * Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by
  classical
  refine NodeDepthCount.sum_eq_finsum_of_forall_le_of_total_eq E _ _ Ttot hTtot _ _ _
    (R.exists_xDepth_pow_eq_valuation_pow_of_reduceFst_eq K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx)
    _ _ _ _ _ _
    (fun Q hQ0 hQπ =>
      ModularCurve.UVCrossingModel.exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem π hπ E hE Q hQ0 hQπ)
    (fun Q hQ => NodeDepthCount.mem_of_length_localizedModule_quotient_ne_zero _ Q hQ)
    (ModularCurve.UVCrossingModel.setOf_horizontal_mem_finite π hπ E hE _
      (NodeDepthCount.ringEquiv_algebraMap_adicCompletion_ne_zero ι f hf))
    (fun r' hr' p' hp' hpE' T' hT' =>
      R.sum_ord_le_finsum_rank_mul_length_of_ringEquiv_uvCrossingModel K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ
        αU hαU hιx f hf r' hr' p' hp' hpE' T' hT')
    htot r hr p hp1 hpE T hT

end NodeDepthCount

open ModularCurve.UVCrossingModel in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (f : ↥(R.nodeIntegersOver K w)) (hf : f ≠ 0)
    (Ttot : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTtot : ∀ V, V ∈ Ttot ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w))
    (htot : ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})))
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ) (hp1 : 1 ≤ p) (hpE : p + 1 ≤ r * E)
    (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hT : ∀ V, V ∈ T ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w ∧
        c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p)) :
    ((∑ V ∈ T, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (r : ℕ∞) * Module.length W (UVCrossingModel W (π ^ E) ⧸ (Q.asIdeal ⊔ Ideal.span {U (π ^ E)})) =
            ((p * Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by
  exact NodeDepthCount.sum_ord_eq_finsum_rank_mul_length_of_total_eq_frame R K w c ϖ hmax hres hVI hwss π hπ E hE ι hιϖ αU
    hαU hιx f hf Ttot hTtot htot r hr p hp1 hpE T hT

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_of_total_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_of_total_eq (solution)
