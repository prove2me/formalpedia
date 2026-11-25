-- Prove2me | solution 1 for GlobalTheory.MassFibre.fibre_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:27.862168+00:00
-- url     : https://prove2.me/submissions/61e46a33-c96b-4cac-bc30-9805d0bebf56

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
import Theorems.Thm_GlobalTheory_MassFibre_inv_encard_eq_relIndex_mul
import Theorems.Thm_GlobalTheory_MassFibre_wt_out_mk
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MassFibre
namespace GlobalTheory.MassFibre
theorem _root_.solution {G : Type} [Group G] (Γ : Subgroup G) {Y Z : Type} [MulAction G Y] [MulAction G Z]
    (f : Y → Z) (S : Set Z) (n : ℕ) (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hfin : ∀ z ∈ S, Finite {y // f y = z} ∧ Nat.card {y // f y = z} = n)
    (hemp : ∀ z, z ∉ S → IsEmpty {y // f y = z})
    (fbar : MulAction.orbitRel.Quotient Γ Y → MulAction.orbitRel.Quotient Γ Z)
    (hfbar : ∀ y, fbar (Quotient.mk _ y) = Quotient.mk _ (f y))
    (O : MulAction.orbitRel.Quotient Γ Z) :
    ∑' P : {P // fbar P = O}, wt Γ (Quotient.out P.1) = (n : ℝ≥0∞) * (if Quotient.out O ∈ S then wt Γ (Quotient.out O) else 0) := by

  classical
  by_cases hz : Quotient.out O ∈ S
  swap
  · rw [if_neg hz, mul_zero]
    haveI : IsEmpty {P // fbar P = O} := by
      refine ⟨fun ⟨P, hP⟩ => ?_⟩
      have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
          = Quotient.mk (MulAction.orbitRel Γ Z) (Quotient.out O) := by
        rw [← hfbar, Quotient.out_eq, Quotient.out_eq, hP]
      obtain ⟨γ, hγ⟩ := Quotient.exact h1
      exact (hemp _ hz).false ⟨(γ⁻¹ : G) • Quotient.out P, by
        rw [hf, ← hγ]; simp [Subgroup.smul_def]⟩
    simp
  rw [if_pos hz]
  obtain ⟨z, hzO⟩ : ∃ z, Quotient.out O = z := ⟨_, rfl⟩
  rw [hzO] at hz ⊢
  have hOz : Quotient.mk (MulAction.orbitRel Γ Z) z = O := by rw [← hzO, Quotient.out_eq]
  let Δ : Subgroup G := Γ ⊓ MulAction.stabilizer G z
  have hΔ : ∀ {g : G}, g ∈ Δ ↔ g ∈ Γ ∧ g • z = z := fun {g} => by
    simp [Δ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  let p : SubMulAction Δ Y :=
    { carrier := f ⁻¹' {z}
      smul_mem' := fun δ y hy => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        rw [Subgroup.smul_def, hf, hy]; exact (hΔ.mp δ.2).2 }
  have hmem : ∀ y : Y, y ∈ p ↔ f y = z := fun y => Iff.rfl
  let e : p ≃ {y // f y = z} := Equiv.subtypeEquivRight hmem
  haveI : Finite {y // f y = z} := (hfin z hz).1
  haveI : Finite p := Finite.of_equiv _ e.symm
  have hcard : Nat.card p = n := (Nat.card_congr e).trans (hfin z hz).2

  let φ : MulAction.orbitRel.Quotient Δ p → {P // fbar P = O} := fun Q =>
    ⟨Quotient.mk _ (Quotient.out Q : p).1, by
      rw [hfbar, (hmem _).mp (Quotient.out Q).2, hOz]⟩
  have hinj : Function.Injective φ := by
    intro Q1 Q2 h
    have h' := congrArg Subtype.val h
    obtain ⟨γ, hγ⟩ := Quotient.exact h'
    have hγΔ : (γ : G) ∈ Δ := by
      refine hΔ.mpr ⟨γ.2, ?_⟩
      have hy1 := (hmem _).mp (Quotient.out Q1).2
      have hy2 := (hmem _).mp (Quotient.out Q2).2
      calc (γ : G) • z = (γ : G) • f (Quotient.out Q2 : p).1 := by rw [hy2]
        _ = f ((γ : G) • (Quotient.out Q2 : p).1) := (hf _ _).symm
        _ = f (Quotient.out Q1 : p).1 := by rw [← hγ]; rfl
        _ = z := hy1
    rw [← Quotient.out_equiv_out]
    refine ⟨⟨γ, hγΔ⟩, ?_⟩
    apply Subtype.ext
    exact hγ
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    have h1 : Quotient.mk (MulAction.orbitRel Γ Z) (f (Quotient.out P))
        = Quotient.mk (MulAction.orbitRel Γ Z) z := by
      rw [← hfbar, Quotient.out_eq, hP, hOz]
    obtain ⟨γ, hγ⟩ := Quotient.exact h1
    let y' : p := ⟨(γ⁻¹ : G) • Quotient.out P, by
      rw [hmem, hf, ← hγ]; simp [Subgroup.smul_def]⟩
    refine ⟨Quotient.mk _ y', Subtype.ext ?_⟩
    obtain ⟨δ, hδ⟩ := (Quotient.mk_out (s := MulAction.orbitRel Δ p) y')
    show Quotient.mk _ _ = P
    conv_rhs => rw [← Quotient.out_eq P]
    apply Quotient.sound
    refine ⟨⟨(δ : G) * (γ : G)⁻¹, Γ.mul_mem (hΔ.mp δ.2).1 (Γ.inv_mem γ.2)⟩, ?_⟩
    rw [← hδ]
    show ((δ : G) * (γ : G)⁻¹) • Quotient.out P = (δ : G) • ((γ⁻¹ : G) • Quotient.out P)
    rw [mul_smul]

  have hw : ∀ y : p, wt Γ (y : Y) = ((MulAction.orbit Δ y).ncard : ℝ≥0∞) * wt Γ z := by
    intro y
    have hy := (hmem _).mp y.2
    have hle : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G) ≤ Δ := by
      intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg
      refine hΔ.mpr ⟨hg.1, ?_⟩
      rw [← hy, ← hf, hg.2]
    have hsub : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).subgroupOf Δ
        = MulAction.stabilizer Δ y := by
      ext δ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, h⟩; exact Subtype.ext h
      · intro h; exact ⟨(hΔ.mp δ.2).1, congrArg Subtype.val h⟩
    have hri : (Γ ⊓ MulAction.stabilizer G (y : Y) : Subgroup G).relIndex Δ
        = (MulAction.orbit Δ y).ncard := by
      rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer]
    have hne : (MulAction.orbit Δ y).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨y, MulAction.mem_orbit_self y⟩ |>.ne'
    unfold wt
    rw [inv_encard_eq_relIndex_mul _ _ hle (hri ▸ hne), hri]
  rw [← (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq]
  haveI : Fintype (MulAction.orbitRel.Quotient Δ p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hterm : ∀ Q : MulAction.orbitRel.Quotient Δ p,
      wt Γ (Quotient.out (Equiv.ofBijective φ ⟨hinj, hsurj⟩ Q).1)
        = ((MulAction.orbit Δ (Quotient.out Q)).ncard : ℝ≥0∞) * wt Γ z := by
    intro Q
    rw [← hw]
    exact wt_out_mk Γ _
  simp_rw [hterm, ← Finset.sum_mul]
  congr 1
  have hsum : ∑ Q : MulAction.orbitRel.Quotient Δ p, (MulAction.orbit Δ (Quotient.out Q)).ncard = n := by
    rw [← hcard, Nat.card_congr (MulAction.selfEquivSigmaOrbits Δ p), Nat.card_sigma]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Nat.card_coe_set_eq]
  rw [← hsum]
  push_cast
  rfl
end GlobalTheory.MassFibre
