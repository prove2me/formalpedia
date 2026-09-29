-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4417b18c-fdda-5d35-9a37-17944dfebd68

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_Patching_CohenMacaulayOfDim
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense
import Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq
import Theorems.Thm_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height
import Theorems.Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim
import Theorems.Thm_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace DIAG
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"
open IsLocalRing

theorem exists_nat_of_add_natCast_eq {x : WithBot ℕ∞} {k n : ℕ} (h : x + (k : WithBot ℕ∞) = n) :
    ∃ d : ℕ, x = d ∧ d + k = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) + (k : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_eq_coe] at h'
      simp at h'
    | coe d => exact ⟨d, rfl, by exact_mod_cast h⟩

theorem exists_nat_ringKrullDim_of_le {S : Type u} [CommRing S] [Nontrivial S] {n : ℕ}
    (h : ringKrullDim S ≤ n) : ∃ d : ℕ, ringKrullDim S = d := by
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim S := ringKrullDim_nonneg_of_nontrivial
  generalize hx : ringKrullDim S = x at h h0
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe] at h'
      simp at h'
    | coe d => exact ⟨d, rfl⟩

theorem height_add_le_of_strictChain {S : Type u} [CommRing S] [IsNoetherianRing S] {n : ℕ}
    (Q : Fin (n + 1) → Ideal S) (hQ : ∀ i, (Q i).IsPrime) (hlt : ∀ j : Fin n, Q j.castSucc < Q j.succ)
    (i : Fin (n + 1)) : (Q 0).height + (i : ℕ) ≤ (Q i).height := by
  refine Fin.induction (by simp) (fun j ih => ?_) i
  haveI := hQ j.castSucc
  have hh := Ideal.height_strict_mono_of_isPrime (hlt j)
  calc (Q 0).height + ((j.succ : Fin (n + 1)) : ℕ)
      = (Q 0).height + (j.castSucc : ℕ) + 1 := by
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, add_assoc]
    _ ≤ (Q j.castSucc).height + 1 := add_le_add ih le_rfl
    _ ≤ (Q j.succ).height := Order.add_one_le_of_lt hh

theorem exists_isPrime_map_le_height_le_one
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing A] [IsNoetherianRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) [IsLocalHom φ] (nA nB : ℕ)
    (_hA : ringKrullDim A = nA) (hB : ringKrullDim B = nB)
    (hCM : ∀ 𝔔 : Ideal A, 𝔔.IsPrime → ringKrullDim (A ⧸ 𝔔) + 𝔔.height = nA)
    (hRS : ((RingHom.ker φ).spanFinrank : WithBot ℕ∞) + nB = nA)
    (p : Ideal A) [hpP : p.IsPrime] (hp : p.height ≤ 1) :
    ∃ P : Ideal B, P.IsPrime ∧ p.map φ ≤ P ∧ P.height ≤ 1 := by
  classical
  set I := RingHom.ker φ with hI
  have hIfg : I.FG := IsNoetherian.noetherian I
  set μ := I.spanFinrank with hμdef
  have hμ : μ + nB = nA := by
    have h := hRS
    exact_mod_cast h

  obtain ⟨k, hk⟩ : ∃ k : ℕ, p.height = k := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hpP.ne_top)
    exact ⟨k, hk.symm⟩
  have hk1 : k ≤ 1 := by rw [hk] at hp; exact_mod_cast hp
  obtain ⟨dAp, hdAp, hdk⟩ : ∃ d : ℕ, ringKrullDim (A ⧸ p) = d ∧ d + k = nA := by
    refine exists_nat_of_add_natCast_eq ?_
    have h := hCM p hpP
    rw [hk] at h
    exact_mod_cast h

  haveI : Nontrivial (A ⧸ p) := ⟨⟨0, 1, fun h => hpP.ne_top (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
  haveI : IsLocalRing (A ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  set J : Ideal (A ⧸ p) := I.map (Ideal.Quotient.mk p) with hJ
  have hJμ : J.spanFinrank ≤ μ := Ideal.spanFinrank_map_le_of_fg (Ideal.Quotient.mk p) hIfg
  have hmA : (maximalIdeal A).map (Ideal.Quotient.mk p) ≠ ⊤ := by
    rw [Ne, Ideal.map_eq_top_iff_of_ker_le (Ideal.Quotient.mk p)
      (by rw [Ideal.mk_ker]; exact le_maximalIdeal hpP.ne_top)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)]
    exact (maximalIdeal.isMaximal A).ne_top
  have hIle : I ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top φ)
  have hJne : J ≠ ⊤ := fun h => hmA (top_le_iff.mp (h ▸ Ideal.map_mono hIle))
  have hJle : J ≤ maximalIdeal (A ⧸ p) := le_maximalIdeal hJne

  have krull := Ideal.height_le_height_add_spanFinrank_of_le hJle
  have hmJ : (maximalIdeal (A ⧸ p)).map (Ideal.Quotient.mk J) ≠ ⊤ := by
    rw [Ne, Ideal.map_eq_top_iff_of_ker_le (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact hJle)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)]
    exact (maximalIdeal.isMaximal (A ⧸ p)).ne_top
  have h2 : ((((maximalIdeal (A ⧸ p)).map (Ideal.Quotient.mk J)).height : ℕ∞) : WithBot ℕ∞)
      ≤ ringKrullDim ((A ⧸ p) ⧸ J) := Ideal.height_le_ringKrullDim_of_ne_top hmJ
  have h1 : (((maximalIdeal (A ⧸ p)).height : ℕ∞) : WithBot ℕ∞) = dAp := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdAp]

  set K : Ideal B := p.map φ with hK
  have hcomp : ((RingHom.quotientKerEquivOfSurjective hφ : A ⧸ I ≃+* B) : A ⧸ I →+* B).comp
      (Ideal.Quotient.mk I) = φ := by
    ext a
    show φ.kerLift (Ideal.Quotient.mk _ a) = φ a
    exact RingHom.kerLift_mk φ a
  have e2 : A ⧸ (I ⊔ p) ≃+* B ⧸ K := by
    refine (DoubleQuot.quotQuotEquivQuotSup I p).symm.trans ?_
    refine Ideal.quotientEquiv (p.map (Ideal.Quotient.mk I)) K (RingHom.quotientKerEquivOfSurjective hφ) ?_
    rw [hK, Ideal.map_map, hcomp]
  have hdimeq : ringKrullDim ((A ⧸ p) ⧸ J) = ringKrullDim (B ⧸ K) := by
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup p I), sup_comm,
      ringKrullDim_eq_of_ringEquiv e2]

  have hKle : K ≤ maximalIdeal B := by
    rw [hK, Ideal.map_le_iff_le_comap]
    exact (le_maximalIdeal hpP.ne_top).trans
      (((IsLocalRing.local_hom_TFAE φ).out 0 3).mp ‹IsLocalHom φ›)
  have hKne : K ≠ ⊤ := fun h => (maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (h ▸ hKle))
  haveI : Nontrivial (B ⧸ K) := ⟨⟨0, 1, fun h => hKne (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
  obtain ⟨dBK, hdBK⟩ : ∃ d : ℕ, ringKrullDim (B ⧸ K) = d :=
    exists_nat_ringKrullDim_of_le ((ringKrullDim_quotient_le K).trans hB.le)

  have hineq : dAp ≤ dBK + μ := by
    have h3 : ((maximalIdeal (A ⧸ p)).height : ℕ∞) ≤
        ((maximalIdeal (A ⧸ p)).map (Ideal.Quotient.mk J)).height + μ :=
      krull.trans (add_le_add le_rfl (by exact_mod_cast hJμ))
    have h3' : ((((maximalIdeal (A ⧸ p)).height : ℕ∞) : WithBot ℕ∞)) ≤
        ((((maximalIdeal (A ⧸ p)).map (Ideal.Quotient.mk J)).height : ℕ∞) : WithBot ℕ∞) + (μ : WithBot ℕ∞) := by
      exact_mod_cast h3
    rw [h1] at h3'
    have h4 : (dAp : WithBot ℕ∞) ≤ ringKrullDim ((A ⧸ p) ⧸ J) + μ := h3'.trans (add_le_add h2 le_rfl)
    rw [hdimeq, hdBK] at h4
    exact_mod_cast h4
  have hnB : nB ≤ dBK + 1 := by omega

  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum (B ⧸ K)), l.length = nB - 1 := by
    refine (Order.le_krullDim_iff).mp ?_
    show (((nB - 1 : ℕ)) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ K)
    rw [hdBK]; exact_mod_cast (by omega : nB - 1 ≤ dBK)
  let Q : Fin (l.length + 1) → Ideal B := fun i => (l i).asIdeal.comap (Ideal.Quotient.mk K)
  have hQprime : ∀ i, (Q i).IsPrime := fun i => Ideal.comap_isPrime _ _
  have hKQ : ∀ i, K ≤ Q i := fun i x hx => by
    show (Ideal.Quotient.mk K) x ∈ (l i).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Submodule.zero_mem _
  have hQlt : ∀ j : Fin l.length, Q j.castSucc < Q j.succ := fun j => by
    have hs : (l j.castSucc).asIdeal < (l j.succ).asIdeal := l.step j
    refine lt_of_le_of_ne (Ideal.comap_mono hs.le) (fun h => hs.ne ?_)
    exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h
  have hchain := height_add_le_of_strictChain Q hQprime hQlt (Fin.last _)

  have htop : ((Q (Fin.last _)).height : ℕ∞) ≤ nB := by
    have h := Ideal.height_le_ringKrullDim_of_ne_top (hQprime (Fin.last _)).ne_top
    rw [hB] at h
    exact_mod_cast h

  obtain ⟨a, ha⟩ : ∃ a : ℕ, (Q 0).height = a := by
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top (hQprime 0).ne_top)
    exact ⟨a, ha.symm⟩
  refine ⟨Q 0, hQprime 0, hKQ 0, ?_⟩
  rw [ha] at hchain ⊢
  simp only [Fin.val_last, hl] at hchain
  have hfin : (a : ℕ∞) + ((nB - 1 : ℕ) : ℕ∞) ≤ nB := hchain.trans htop
  have : a + (nB - 1) ≤ nB := by exact_mod_cast hfin
  exact_mod_cast (by omega : a ≤ 1)

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace DIAG
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem coheight_fromSpecStalk {X : Scheme.{u}} (x : X) (p : ↥(Spec (X.presheaf.stalk x))) :
    Order.coheight ((X.fromSpecStalk x).base p) = Order.coheight p := by
  have hemb := (X.fromSpecStalk x).isEmbedding
  have hspec_iff : ∀ a b : ↥(Spec (X.presheaf.stalk x)),
      (X.fromSpecStalk x).base a ⤳ (X.fromSpecStalk x).base b ↔ a ⤳ b :=
    fun a b => hemb.specializes_iff
  have hstrict : StrictMono (α := ↥(Spec (X.presheaf.stalk x))) (X.fromSpecStalk x).base :=
    fun a b hab => ⟨(hspec_iff b a).mpr hab.1, fun hle => hab.2 ((hspec_iff a b).mp hle)⟩
  have hpx : (X.fromSpecStalk x).base p ⤳ x := by
    have hmem : (X.fromSpecStalk x).base p ∈ Set.range (X.fromSpecStalk x).base := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem; exact hmem
  apply le_antisymm
  · rw [Order.coheight_le_iff']
    intro l hl_head
    have hmem : ∀ j, ∃ q : ↥(Spec (X.presheaf.stalk x)),
        (X.fromSpecStalk x).base q = l.toFun j := by
      intro j
      have hle : (X.fromSpecStalk x).base p ≤ l.toFun j := hl_head ▸ LTSeries.head_le l j
      have hgen : l.toFun j ⤳ x :=
        Specializes.trans (show l.toFun j ⤳ (X.fromSpecStalk x).base p from hle) hpx
      have hmem' : l.toFun j ∈ Set.range (X.fromSpecStalk x).base := by
        rw [Scheme.range_fromSpecStalk]; exact hgen
      exact hmem'
    choose g hg using hmem
    have hgstep : ∀ j : Fin l.length, g j.castSucc < g j.succ := by
      intro j
      have hl_step := l.step j
      refine ⟨(hspec_iff _ _).mp ?_, fun hba => ?_⟩
      · rw [hg, hg]; exact hl_step.1
      · exact hl_step.2 ((hg j.succ) ▸ (hg j.castSucc) ▸ (hspec_iff _ _).mpr hba)
    set l' : LTSeries ↥(Spec (X.presheaf.stalk x)) := ⟨l.length, g, hgstep⟩ with hl'
    have hl'_head : l'.head = p :=
      hemb.injective ((hg 0).trans (hl_head ▸ rfl))
    calc (l.length : ℕ∞) = l'.length := rfl
      _ ≤ Order.coheight l'.head := Order.length_le_coheight_head
      _ = Order.coheight p := by rw [hl'_head]
  · rw [Order.coheight_le_iff']
    intro l hl_head
    have := Order.length_le_coheight_head (p := l.map (X.fromSpecStalk x).base hstrict)
    rwa [LTSeries.head_map, hl_head, LTSeries.map_length] at this

theorem ringKrullDim_stalk_fromSpecStalk {X : Scheme.{u}} (x : X) (p : ↥(Spec (X.presheaf.stalk x))) :
    ringKrullDim (X.presheaf.stalk ((X.fromSpecStalk x).base p)) = p.asIdeal.height := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, coheight_fromSpecStalk,
    ← AlgebraicGeometry.idealHeight_eq_coheight]

theorem exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height
    {R : Type u} [CommRing R] {T : Scheme.{u}} [IsLocallyNoetherian T]
    (t : T ⟶ Spec (CommRingCat.of R)) [IsLocallyNoetherian (pullback t t)] (y : T)
    (nA : ℕ) (hA : ringKrullDim ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) = nA)
    (hCM : ∀ 𝔔 : Ideal ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)), 𝔔.IsPrime →
      ringKrullDim (((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) ⧸ 𝔔) + 𝔔.height = nA)
    (hRS : ((RingHom.ker ((pullback.diagonal t).stalkMap y).hom).spanFinrank : WithBot ℕ∞)
        + ringKrullDim (T.presheaf.stalk y)
      = ringKrullDim ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)))
    (η : ↑(pullback t t)) (hη : η ⤳ (pullback.diagonal t).base y)
    (hdim : ringKrullDim ((pullback t t).presheaf.stalk η) ≤ 1) :
    ∃ ξ : T, ξ ⤳ y ∧ ringKrullDim (T.presheaf.stalk ξ) ≤ 1 ∧ η ⤳ (pullback.diagonal t).base ξ := by
  classical
  haveI : IsNoetherianRing ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) := inferInstance
  haveI : IsNoetherianRing (T.presheaf.stalk y) := inferInstance
  haveI : IsLocalHom ((pullback.diagonal t).stalkMap y).hom := inferInstance
  have hφ : Function.Surjective ((pullback.diagonal t).stalkMap y).hom :=
    (pullback.diagonal t).stalkMap_surjective y

  obtain ⟨nB, hB, hμ⟩ : ∃ nB : ℕ, ringKrullDim (T.presheaf.stalk y) = nB ∧
      nB + (RingHom.ker ((pullback.diagonal t).stalkMap y).hom).spanFinrank = nA := by
    refine exists_nat_of_add_natCast_eq ?_
    rw [add_comm, hRS, hA]
  have hRS' : ((RingHom.ker ((pullback.diagonal t).stalkMap y).hom).spanFinrank : WithBot ℕ∞) + nB = nA := by
    exact_mod_cast (show (RingHom.ker ((pullback.diagonal t).stalkMap y).hom).spanFinrank + nB = nA by omega)

  obtain ⟨p, hp⟩ : ∃ p : ↥(Spec ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y))),
      ((pullback t t).fromSpecStalk ((pullback.diagonal t).base y)).base p = η := by
    have hmem : η ∈ Set.range ((pullback t t).fromSpecStalk ((pullback.diagonal t).base y)).base := by
      rw [Scheme.range_fromSpecStalk]; exact hη
    exact hmem
  have hp_ht : p.asIdeal.height ≤ 1 := by
    have h := ringKrullDim_stalk_fromSpecStalk ((pullback.diagonal t).base y) p
    rw [hp] at h
    have h' : (p.asIdeal.height : WithBot ℕ∞) ≤ 1 := h ▸ hdim
    exact_mod_cast h'

  obtain ⟨P, hPprime, hPle, hPht⟩ := exists_isPrime_map_le_height_le_one
    ((pullback.diagonal t).stalkMap y).hom hφ nA nB hA hB hCM hRS' p.asIdeal hp_ht

  let qP : ↥(Spec (T.presheaf.stalk y)) := ⟨P, hPprime⟩
  refine ⟨(T.fromSpecStalk y).base qP, ?_, ?_, ?_⟩
  · have hmem : (T.fromSpecStalk y).base qP ∈ Set.range (T.fromSpecStalk y).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem; exact hmem
  · rw [ringKrullDim_stalk_fromSpecStalk y qP]
    exact_mod_cast hPht
  · have hnat : (pullback.diagonal t).base ((T.fromSpecStalk y).base qP) =
        ((pullback t t).fromSpecStalk ((pullback.diagonal t).base y)).base
          ((Spec.map ((pullback.diagonal t).stalkMap y)).base qP) := by
      have key := congrArg (fun k => (Scheme.Hom.toLRSHom k).base qP)
        (Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.diagonal t) (x := y))
      exact key.symm
    rw [hnat, ← hp]
    refine ((pullback t t).fromSpecStalk ((pullback.diagonal t).base y)).isEmbedding.specializes_iff.mpr ?_
    refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
    show p.asIdeal ≤ ((Spec.map ((pullback.diagonal t).stalkMap y)).base qP).asIdeal
    exact Ideal.map_le_iff_le_comap.mp hPle

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace DIAG
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

scoped instance isDomain_sections_spec (k : Type u) [Field k] :
    IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isDomain k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isIntegrallyClosed_sections_spec (k : Type u) [Field k] :
    IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
  IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm

theorem isDomain_and_isIntegrallyClosed_stalk_of_field (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g x

theorem isReduced_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := (isDomain_and_isIntegrallyClosed_stalk_of_field k g x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

theorem exists_specializes_ringKrullDim_stalk_le_one {X : Scheme.{u}} (x : X) :
    ∃ ξ : X, ξ ⤳ x ∧ ringKrullDim (X.presheaf.stalk ξ) ≤ 1 := by
  have hZ : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hZc : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  let ξ := hZ.genericPoint
  have hξ : IsGenericPoint ξ (irreducibleComponent x) := hZ.isGenericPoint_genericPoint hZc
  refine ⟨ξ, hξ.specializes mem_irreducibleComponent, ?_⟩
  have hmax : IsMax ξ := by
    intro b hb

    have hbξ : b ⤳ ξ := hb
    have hsub : irreducibleComponent x ⊆ closure {b} := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hbξ)) isClosed_closure
    have heq : closure {b} = irreducibleComponent x :=
      eq_irreducibleComponent (isIrreducible_singleton.closure).isPreirreducible hsub
    show ξ ⤳ b
    rw [specializes_iff_mem_closure, hξ.def, ← heq]
    exact subset_closure (Set.mem_singleton b)
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax]
  exact_mod_cast zero_le_one

theorem dense_of_forall_ringKrullDim_le_one {X : Scheme.{u}} (V : X.Opens)
    (hV : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V) : Dense (V : Set X) := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨x, hx⟩
  obtain ⟨ξ, hξx, hξ⟩ := exists_specializes_ringKrullDim_stalk_le_one x
  exact ⟨ξ, hξx.mem_open hO hx, hV ξ hξ⟩

theorem dense_inf_preimage_of_dense {R : Type u} [CommRing R] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) [UniversallyOpen t] (V : T.Opens) (hV : Dense (V : Set T)) :
    Dense ((((pullback.fst t t) ⁻¹ᵁ V ⊓ (pullback.snd t t) ⁻¹ᵁ V : (pullback t t).Opens)) : Set ↑(pullback t t)) := by
  have h1 : Dense (((pullback.fst t t) ⁻¹ᵁ V : (pullback t t).Opens) : Set ↑(pullback t t)) :=
    hV.preimage (Scheme.Hom.isOpenMap (pullback.fst t t))
  have h2 : Dense (((pullback.snd t t) ⁻¹ᵁ V : (pullback t t).Opens) : Set ↑(pullback t t)) :=
    hV.preimage (Scheme.Hom.isOpenMap (pullback.snd t t))
  rw [TopologicalSpace.Opens.coe_inf]
  exact h1.inter_of_isOpen_left h2 ((pullback.fst t t) ⁻¹ᵁ V).2

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian"

noncomputable section
namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace C3
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian TopologicalSpace Topology"

variable {k : Type u} [Field k] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}

theorem eq_one_of_mul_eq (G : RelativeGroupLaw k f) {S : Scheme.{u}}
    (g : S ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver g f) (h : G.mul g x y = y) : x = G.one g := by
  calc x = G.mul g x (G.one g) := (G.mul_one g x).symm
    _ = G.mul g x (G.mul g y (G.inv g y)) := by rw [G.mul_inv_cancel]
    _ = G.mul g (G.mul g x y) (G.inv g y) := by rw [G.mul_assoc]
    _ = G.one g := by rw [h, G.mul_inv_cancel]

omit [Field k] in

theorem isDominant_homOfLE_inf {X : Scheme.{u}} (U V : X.Opens) (hV : Dense (V : Set X)) :
    IsDominant (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) := by
  rw [isDominant_iff]
  have hrange : Set.range (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).base =
      (Subtype.val : ↥U → X) ⁻¹' ((U ⊓ V : X.Opens) : Set X) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      show ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)).base x).1 ∈ ((U ⊓ V : X.Opens) : Set X)
      rw [Scheme.homOfLE_apply]
      exact x.2
    · intro hy
      refine ⟨⟨y.1, hy⟩, ?_⟩
      apply Subtype.ext
      rw [Scheme.homOfLE_apply]
  intro y
  rw [hrange]
  have hcl : (Subtype.val ⁻¹' closure ((U ⊓ V : X.Opens) : Set X) : Set ↥U) =
      closure (Subtype.val ⁻¹' ((U ⊓ V : X.Opens) : Set X)) :=
    (IsOpen.isOpenMap_subtype_val U.2).preimage_closure_eq_closure_preimage continuous_subtype_val _
  have hy : y ∈ closure (Subtype.val ⁻¹' ((U ⊓ V : X.Opens) : Set X) : Set ↥U) := by
    rw [← hcl]
    show y.1 ∈ closure ((U : Set X) ∩ (V : Set X))
    exact hV.open_subset_closure_inter U.2 y.2
  exact hy

theorem diagonal_restrict_comp_eq_unit (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV : Dense (V : Set T)) (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hrec : ∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) :
    (pullback.diagonal t ∣_ W) ≫ d.1 =
      ((pullback.diagonal t) ⁻¹ᵁ W).ι ≫ t ≫ (G.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
  haveI : IsReduced T := GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isReduced_of_smooth k t
  set U : T.Opens := (pullback.diagonal t) ⁻¹ᵁ W with hU
  haveI : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  set e := G.one (𝟙 (Spec (CommRingCat.of k))) with he
  have hΔfst : (pullback.diagonal t ∣_ W) ≫ W.ι ≫ pullback.fst t t = U.ι := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hΔsnd : (pullback.diagonal t ∣_ W) ≫ W.ι ≫ pullback.snd t t = U.ι := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have hL : ((pullback.diagonal t ∣_ W) ≫ d.1) ≫ f = U.ι ≫ t := by
    rw [Category.assoc, d.2]
    simp only [← Category.assoc]
    rw [Category.assoc (pullback.diagonal t ∣_ W), hΔfst]
  have hR : (U.ι ≫ t ≫ e.1) ≫ f = U.ι ≫ t := by
    rw [Category.assoc, Category.assoc, e.2, Category.comp_id]
  haveI := isDominant_homOfLE_inf U V hV
  refine ext_of_isDominant_of_isSeparated f (hL.trans hR.symm) (T.homOfLE (inf_le_left : U ⊓ V ≤ U)) ?_

  set a : (U ⊓ V).toScheme ⟶ W.toScheme := T.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ (pullback.diagonal t ∣_ W)
    with ha
  set b : (U ⊓ V).toScheme ⟶ V.toScheme := T.homOfLE (inf_le_right : U ⊓ V ≤ V) with hb0
  have hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι := by
    rw [ha, Category.assoc, hΔfst, Scheme.homOfLE_ι, hb0, Scheme.homOfLE_ι]
  have hc : a ≫ W.ι ≫ pullback.snd t t = b ≫ V.ι := by
    rw [ha, Category.assoc, hΔsnd, Scheme.homOfLE_ι, hb0, Scheme.homOfLE_ι]
  have key := hrec _ a b b hb hc
  have hone := eq_one_of_mul_eq G _ _ _ key
  have h1 : a ≫ d.1 = (a ≫ W.ι ≫ pullback.fst t t ≫ t) ≫ e.1 := by
    have h2 := congrArg Subtype.val hone
    rw [← G.one_natural (𝟙 (Spec (CommRingCat.of k))) (a ≫ W.ι ≫ pullback.fst t t ≫ t)
      (a ≫ W.ι ≫ pullback.fst t t ≫ t) (Category.comp_id _)] at h2
    exact h2
  calc T.homOfLE _ ≫ (pullback.diagonal t ∣_ W) ≫ d.1 = a ≫ d.1 := by rw [ha, Category.assoc]
    _ = (a ≫ W.ι ≫ pullback.fst t t ≫ t) ≫ e.1 := h1
    _ = T.homOfLE _ ≫ U.ι ≫ t ≫ e.1 := by
        rw [ha]
        simp only [Category.assoc]
        rw [reassoc_of% hΔfst]

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian Topology"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace C3b
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem exists_rationalMap_component_affine
    {k : Type u} [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV1 : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hVV : ∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V → p ∈ W)
    (hrec : ∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)
    (hmax : ∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι → a' ≫ d'.1 = a ≫ d.1)
    (y : T) (P₀ : (pullback t t).Opens) [IrreducibleSpace (P₀ : Scheme.{u})]
    (hyP₀ : (pullback.diagonal t).base y ∈ P₀)
    (H : A.Opens) (hHe : ∀ s : ↥(Spec (CommRingCat.of k)), (G.one (𝟙 (Spec (CommRingCat.of k)))).1.base s ∈ H) :
    ∃ u : (P₀ : Scheme.{u}) ⤏ (H : Scheme.{u}),
      (∀ p : ↥P₀, p ∈ u.domain → P₀.ι.base p ∈ W) ∧
      (∀ ξ : T, ξ ∈ V → ξ ⤳ y →
        ∃ hξ : (pullback.diagonal t).base ξ ∈ P₀, (⟨(pullback.diagonal t).base ξ, hξ⟩ : ↥P₀) ∈ u.domain) := by
  classical

  haveI : IsReduced (pullback t t) :=
    GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isReduced_of_smooth k (pullback.fst t t ≫ t)
  have hV : Dense (V : Set T) :=
    GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.dense_of_forall_ringKrullDim_le_one V hV1

  have hC3a := GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3.diagonal_restrict_comp_eq_unit
    G t V hV v W d hrec
  have hdΔ : ∀ (θ : T) (hθ : (pullback.diagonal t).base θ ∈ W),
      d.1.base ⟨(pullback.diagonal t).base θ, hθ⟩ ∈ H := by
    intro θ hθ
    have hθ' : θ ∈ (pullback.diagonal t) ⁻¹ᵁ W := by rw [Scheme.Hom.mem_preimage]; exact hθ
    have e1 := congrArg (fun φ => φ.base ⟨θ, hθ'⟩) hC3a
    simp only [Scheme.Hom.comp_apply] at e1
    have e2 : (pullback.diagonal t ∣_ W).base ⟨θ, hθ'⟩ = ⟨(pullback.diagonal t).base θ, hθ⟩ :=
      Subtype.ext (morphismRestrict_base_coe _ _ _)
    rw [e2] at e1
    rw [e1]
    exact hHe _

  have key : ∀ θ : T, θ ∈ V → θ ⤳ y →
      (pullback.diagonal t).base θ ∈ P₀ ∧ (pullback.diagonal t).base θ ∈ W := by
    intro θ hθV hθy
    refine ⟨(hθy.map (Scheme.Hom.continuous (pullback.diagonal t))).mem_open P₀.2 hyP₀, hVV _ ?_ ?_⟩
    · rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]; exact hθV
    · rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]; exact hθV

  obtain ⟨θ₀, hθ₀y, hθ₀dim⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_specializes_ringKrullDim_stalk_le_one y
  have hθ₀V : θ₀ ∈ V := hV1 θ₀ hθ₀dim

  let WH : (pullback t t).Opens := W.ι ''ᵁ (d.1 ⁻¹ᵁ H)
  have hWH_le : WH ≤ W := by
    rintro q ⟨w, -, rfl⟩; exact w.2
  let U₀ : (P₀ : Scheme.{u}).Opens := P₀.ι ⁻¹ᵁ WH
  have hrange1 : Set.range (U₀.ι ≫ P₀.ι).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hWH_le ((Scheme.Hom.mem_preimage _).mp z.2)
  let ℓ := IsOpenImmersion.lift W.ι (U₀.ι ≫ P₀.ι) hrange1
  have hℓ : ℓ ≫ W.ι = U₀.ι ≫ P₀.ι := IsOpenImmersion.lift_fac _ _ _
  have hℓmem : ∀ z : ↥U₀, ℓ.base z ∈ d.1 ⁻¹ᵁ H := by
    intro z
    have hz : P₀.ι.base (U₀.ι.base z) ∈ WH := (Scheme.Hom.mem_preimage _).mp z.2
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = ℓ.base z := by
      apply W.ι.isOpenEmbedding.injective
      refine hwz.trans ?_
      show P₀.ι.base (U₀.ι.base z) = W.ι.base (ℓ.base z)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hℓ]
    rw [← this]; exact hw
  have hrange2 : Set.range (ℓ ≫ d.1).base ⊆ Set.range H.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (Scheme.Hom.mem_preimage _).mp (hℓmem z)
  let rep : (U₀ : Scheme.{u}) ⟶ (H : Scheme.{u}) := IsOpenImmersion.lift H.ι (ℓ ≫ d.1) hrange2
  have hrep : rep ≫ H.ι = ℓ ≫ d.1 := IsOpenImmersion.lift_fac _ _ _

  have hΔU₀ : ∀ (θ : T) (hθV : θ ∈ V) (hθy : θ ⤳ y),
      (⟨(pullback.diagonal t).base θ, (key θ hθV hθy).1⟩ : ↥P₀) ∈ U₀ := by
    intro θ hθV hθy
    show P₀.ι.base _ ∈ WH
    exact ⟨⟨(pullback.diagonal t).base θ, (key θ hθV hθy).2⟩,
      (Scheme.Hom.mem_preimage _).mpr (hdΔ θ (key θ hθV hθy).2), rfl⟩
  have hU₀dense : Dense (SetLike.coe U₀) :=
    IsOpen.dense U₀.2 ⟨⟨(pullback.diagonal t).base θ₀, (key θ₀ hθ₀V hθ₀y).1⟩, hΔU₀ θ₀ hθ₀V hθ₀y⟩
  let g₀ : (P₀ : Scheme.{u}).PartialMap (H : Scheme.{u}) := ⟨U₀, hU₀dense, rep⟩
  refine ⟨g₀.toRationalMap, ?_, ?_⟩
  ·
    intro p hp
    obtain ⟨g, hpg, hgeq⟩ := Scheme.RationalMap.mem_domain.mp hp
    rw [Scheme.PartialMap.toRationalMap_eq_iff] at hgeq
    obtain ⟨W₀, hW₀d, hW₀g, hW₀g₀, hagree⟩ := hgeq
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom] at hagree
    change (P₀ : Scheme.{u}).homOfLE hW₀g ≫ g.hom = (P₀ : Scheme.{u}).homOfLE hW₀g₀ ≫ rep at hagree

    haveI : IsDominant ((P₀ : Scheme.{u}).homOfLE hW₀g) := by
      rw [isDominant_iff]
      have hrange : Set.range ((P₀ : Scheme.{u}).homOfLE hW₀g).base =
          (Subtype.val : ↥g.domain → ↥P₀) ⁻¹' (SetLike.coe W₀) := by
        ext q; constructor
        · rintro ⟨x, rfl⟩
          show (((P₀ : Scheme.{u}).homOfLE hW₀g).base x).1 ∈ (SetLike.coe W₀)
          rw [Scheme.homOfLE_apply]; exact x.2
        · intro hq; refine ⟨⟨q.1, hq⟩, Subtype.ext ?_⟩; rw [Scheme.homOfLE_apply]
      intro q
      rw [hrange]
      have hcl : (Subtype.val ⁻¹' closure (SetLike.coe W₀) : Set ↥g.domain) =
          closure (Subtype.val ⁻¹' (SetLike.coe W₀)) :=
        (IsOpen.isOpenMap_subtype_val g.domain.2).preimage_closure_eq_closure_preimage continuous_subtype_val _
      have hq : q ∈ closure (Subtype.val ⁻¹' (SetLike.coe W₀) : Set ↥g.domain) := by
        rw [← hcl]; exact hW₀d q.1
      exact hq
    have hℓR : ℓ ≫ d.1 ≫ f = U₀.ι ≫ P₀.ι ≫ pullback.fst t t ≫ t := by
      rw [d.2, ← Category.assoc, hℓ, Category.assoc]
    have hgover : g.hom ≫ H.ι ≫ f = g.domain.ι ≫ P₀.ι ≫ pullback.fst t t ≫ t := by
      refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _)
        ((P₀ : Scheme.{u}).homOfLE hW₀g) ?_
      rw [← Category.assoc, hagree, Category.assoc, ← Category.assoc rep, hrep, Category.assoc, hℓR,
        ← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc ((P₀ : Scheme.{u}).homOfLE hW₀g), Scheme.homOfLE_ι]

    let W' : (pullback t t).Opens := P₀.ι ''ᵁ g.domain
    let iso := Scheme.Hom.isoImage P₀.ι g.domain
    let d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f :=
      ⟨iso.inv ≫ g.hom ≫ H.ι, by
        rw [Category.assoc, Category.assoc, hgover, ← Category.assoc iso.inv,
          ← Category.assoc (iso.inv ≫ g.domain.ι), Category.assoc iso.inv, Scheme.Hom.isoImage_inv_ι]⟩
    let W₀' : (pullback t t).Opens := P₀.ι ''ᵁ W₀
    have hW₀'W : W₀' ≤ W := by
      rintro _ ⟨q, hq, rfl⟩
      exact hWH_le ((Scheme.Hom.mem_preimage _).mp (hW₀g₀ hq))
    have hW₀'W' : W₀' ≤ W' := by
      rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hW₀g hq, rfl⟩
    have h₀ : W₀' ≤ W ⊓ W' := le_inf hW₀'W hW₀'W'
    have hdense' : ((W' : (pullback t t).Opens) : Set ↑(pullback t t)) ⊆ closure (W₀' : Set ↑(pullback t t)) := by
      rintro _ ⟨q, -, rfl⟩
      have hq : q ∈ closure (SetLike.coe W₀) := hW₀d q
      have := image_closure_subset_closure_image (Scheme.Hom.continuous P₀.ι) ⟨q, hq, rfl⟩
      rwa [← Scheme.Hom.coe_image] at this
    have hagree' : (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 =
        (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ d'.1 := by
      let j := Scheme.Hom.isoImage P₀.ι W₀
      rw [← cancel_epi j.hom]

      have hL : j.hom ≫ (pullback t t).homOfLE (h₀.trans inf_le_left) = (P₀ : Scheme.{u}).homOfLE hW₀g₀ ≫ ℓ := by
        rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι, Category.assoc, hℓ,
          ← Category.assoc, Scheme.homOfLE_ι]

      have hR : j.hom ≫ (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ iso.inv =
          (P₀ : Scheme.{u}).homOfLE hW₀g := by
        rw [← cancel_mono (g.domain.ι ≫ P₀.ι), Category.assoc, Category.assoc, Scheme.Hom.isoImage_inv_ι,
          Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι, ← Category.assoc, Scheme.homOfLE_ι]
      rw [← Category.assoc, hL, Category.assoc, ← hrep, ← Category.assoc, ← hagree, Category.assoc]
      show _ = j.hom ≫ (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ iso.inv ≫ g.hom ≫ H.ι
      rw [← Category.assoc j.hom, ← Category.assoc (j.hom ≫ _), Category.assoc j.hom, hR]
    obtain ⟨hW'W, -⟩ := hmax W' d' W₀' h₀ hdense' hagree'
    exact hW'W ⟨p, hpg, rfl⟩
  ·
    intro ξ hξV hξy
    exact ⟨(key ξ hξV hξy).1, g₀.le_domain_toRationalMap (hΔU₀ ξ hξV hξy)⟩

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3b
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace DIAG
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem exists_nat_ringKrullDim_eq_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    ∃ n : ℕ, ringKrullDim A = n :=
  ⟨(maximalIdeal A).spanFinrank, (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm⟩

theorem isCohenMacaulayOfDim_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (n : ℕ) (hA : ringKrullDim A = n) : IsCohenMacaulayOfDim A n := by
  haveI : IsNoetherianRing A := inferInstance
  refine ⟨hA, ?_⟩
  have h := IsRegularLocalRing.depth_self_eq_ringKrullDim A
  rw [hA] at h
  have h' : ((Module.depth A A : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [h, WithBot.coe_natCast]
  exact WithBot.coe_injective h'

theorem ringKrullDim_quotient_add_height_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (n : ℕ) (hA : ringKrullDim A = n) :
    ∀ 𝔔 : Ideal A, 𝔔.IsPrime → ringKrullDim (A ⧸ 𝔔) + 𝔔.height = n := by
  intro 𝔔 h𝔔
  haveI : IsNoetherianRing A := inferInstance
  exact IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height
    (isCohenMacaulayOfDim_of_isRegularLocalRing A n hA) 𝔔

theorem krull_transfer_inputs
    (k : Type u) [Field k]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t] (y : T) :
    ∃ nA : ℕ, ringKrullDim ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) = nA ∧
      (∀ 𝔔 : Ideal ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)), 𝔔.IsPrime →
        ringKrullDim (((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) ⧸ 𝔔) + 𝔔.height = nA) ∧
      ((RingHom.ker ((pullback.diagonal t).stalkMap y).hom).spanFinrank : WithBot ℕ∞)
          + ringKrullDim (T.presheaf.stalk y)
        = ringKrullDim ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) := by
  haveI hregP : IsRegularLocalRing ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := pullback.fst t t ≫ t) _
  haveI hregT : IsRegularLocalRing (T.presheaf.stalk y) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) y
  obtain ⟨nA, hA⟩ := exists_nat_ringKrullDim_eq_of_isRegularLocalRing
    ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y))
  refine ⟨nA, hA, ringKrullDim_quotient_add_height_of_isRegularLocalRing _ nA hA, ?_⟩
  exact IsRegularLocalRing.spanFinrank_ker_add_ringKrullDim_eq ((pullback.diagonal t).stalkMap y).hom
    ((pullback.diagonal t).stalkMap_surjective y)

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace DIAG
namespace B
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem isIntegral_and_isLocallyNoetherian_and_isIntegrallyClosed_of_isIrreducible
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsIrreducible (U : Set X)) :
    IsIntegral (U : Scheme.{u}) ∧ IsLocallyNoetherian (U : Scheme.{u}) ∧
      ∀ p : ↥U, IsIntegrallyClosed ((U : Scheme.{u}).presheaf.stalk p) := by
  haveI : IsReduced X := by
    haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
      haveI := (hX x).1
      inferInstance
    exact isReduced_of_isReduced_stalk X
  haveI : IrreducibleSpace (U : Scheme.{u}) := Subtype.irreducibleSpace hU
  refine ⟨(isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨‹_›, inferInstance⟩, inferInstance, ?_⟩
  intro p
  haveI := (hX p.1).2
  exact IsIntegrallyClosed.of_equiv (U.stalkIso p).symm.commRingCatIsoToRingEquiv

theorem exists_isAffineOpen_forall_mem_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} (e : Spec (CommRingCat.of R) ⟶ A) :
    ∃ H : A.Opens, IsAffineOpen H ∧ ∀ s : ↥(Spec (CommRingCat.of R)), e.base s ∈ H := by
  obtain ⟨_, ⟨H, hH, rfl⟩, hxH, -⟩ := A.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e.base (IsLocalRing.closedPoint R))) isOpen_univ
  exact ⟨H, hH, fun s =>
    ((IsLocalRing.specializes_closedPoint s).map e.base.hom.continuous).mem_open H.2 hxH⟩

theorem specializes_ι_of_specializes {X : Scheme.{u}} (U : X.Opens) {a b : ↥U} (h : a ⤳ b) :
    U.ι.base a ⤳ U.ι.base b :=
  h.map U.ι.base.hom.continuous

theorem specializes_of_specializes_ι {X : Scheme.{u}} (U : X.Opens) {a b : ↥U} (h : U.ι.base a ⤳ U.ι.base b) :
    a ⤳ b :=
  U.ι.isOpenEmbedding.isInducing.specializes_iff.mp h

theorem ringKrullDim_stalk_ι {X : Scheme.{u}} (U : X.Opens) (a : ↥U) :
    ringKrullDim (X.presheaf.stalk (U.ι.base a)) = ringKrullDim ((U : Scheme.{u}).presheaf.stalk a) :=
  ringKrullDim_eq_of_ringEquiv (U.stalkIso a).symm.commRingCatIsoToRingEquiv

theorem ι_base_apply_mk {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) : U.ι.base ⟨x, hx⟩ = x :=
  rfl

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mk inv mul exists_isGreatest_opens_difference_extension_of_dense"
namespace WeilExtField
namespace DIAG
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian Topology"

theorem diag_assembly
    (k : Type u) [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV1 : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) := by
  classical
  have hV : Dense (V : Set T) := dense_of_forall_ringKrullDim_le_one V hV1

  obtain ⟨W, d, hVV, hrec, hmax⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense k G t V hV v
  refine ⟨W, d, ?_, hrec⟩
  intro y
  by_contra hy

  set q : ↑(pullback t t) := (pullback.diagonal t).base y with hq_def

  haveI hTln : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  haveI hPln : IsLocallyNoetherian (pullback t t) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst t t ≫ t)

  have hPn : ∀ p : ↑(pullback t t), IsDomain ((pullback t t).presheaf.stalk p) ∧
      IsIntegrallyClosed ((pullback t t).presheaf.stalk p) := fun p =>
    isDomain_and_isIntegrallyClosed_stalk_of_field k (pullback.fst t t ≫ t) p

  obtain ⟨hP₀open, -⟩ :=
    AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk (X := pullback t t) (fun p => (hPn p).1) q
  set P₀ : (pullback t t).Opens := ⟨irreducibleComponent q, hP₀open⟩ with hP₀_def
  have hqP₀ : q ∈ P₀ := mem_irreducibleComponent

  obtain ⟨hP₀int, hP₀ln, hP₀n⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.isIntegral_and_isLocallyNoetherian_and_isIntegrallyClosed_of_isIrreducible
      hPn P₀ (isIrreducible_irreducibleComponent (x := q))
  haveI : IsIntegral (P₀ : Scheme.{u}) := hP₀int
  haveI : IsLocallyNoetherian (P₀ : Scheme.{u}) := hP₀ln

  obtain ⟨H, hHaff, hHe⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.exists_isAffineOpen_forall_mem_of_isLocalRing
      (G.one (𝟙 (Spec (CommRingCat.of k)))).1
  haveI : IsAffine (H : Scheme.{u}) := hHaff

  obtain ⟨u, hu_dom_le_W, hu_diag⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3b.exists_rationalMap_component_affine
      G t V hV1 v W d hVV hrec hmax y P₀ hqP₀ H hHe
  have hq_dom : (⟨q, hqP₀⟩ : ↥P₀) ∉ u.domain := by
    intro h
    have h' := hu_dom_le_W _ h
    rw [GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.ι_base_apply_mk] at h'
    exact hy h'

  obtain ⟨z, hz_dom, hzq, hz_dim⟩ :=
    AlgebraicGeometry.Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain
      hP₀n u ⟨q, hqP₀⟩ hq_dom

  have hηq : P₀.ι.base z ⤳ q := by
    have h := GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.specializes_ι_of_specializes P₀ hzq
    rwa [GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.ι_base_apply_mk] at h
  have hη_dim : ringKrullDim ((pullback t t).presheaf.stalk (P₀.ι.base z)) ≤ 1 := by
    rw [GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.ringKrullDim_stalk_ι]; exact hz_dim

  obtain ⟨nA, hA, hCM, hRS⟩ := krull_transfer_inputs k t y
  obtain ⟨ξ, hξy, hξ_dim, hzξ⟩ :=
    exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height t y nA hA hCM hRS
      (P₀.ι.base z) hηq hη_dim

  have hξV : ξ ∈ V := hV1 ξ hξ_dim

  obtain ⟨hξP₀, hξ_dom⟩ := hu_diag ξ hξV hξy
  refine hz_dom ?_
  have hzξ' : z ⤳ (⟨(pullback.diagonal t).base ξ, hξP₀⟩ : ↥P₀) := by
    refine GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.specializes_of_specializes_ι P₀ ?_
    rw [GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.ι_base_apply_mk]
    exact hzξ
  exact hzξ'.mem_open u.domain.2 hξ_dom

end GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG"

theorem solution
    (k : Type u) [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) :=
  GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.diag_assembly k G t V hV v

end S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one (solution)
