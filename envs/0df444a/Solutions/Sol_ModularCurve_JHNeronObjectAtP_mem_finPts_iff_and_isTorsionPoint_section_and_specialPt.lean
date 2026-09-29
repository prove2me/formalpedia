-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/45db326f-9bb8-5e4a-bf64-c589253ea7d1

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

namespace N3Aux

variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' _ _ = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem nsmul_natural {T T' : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.nsmul t n x) =
      G.nsmul t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, G.one_natural]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, G.mul_natural, ih]

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f)
    (h : G.mul t a a = a) : a = G.one t := by
  have h1 : G.mul t (G.inv t a) (G.mul t a a) = G.mul t (G.inv t a) a := by rw [h]
  rw [← G.mul_assoc, G.inv_mul_cancel, G.one_mul] at h1
  exact h1

end N3Aux

open N3Aux

theorem isDominant_barPt (A : ValuationSubring (AlgebraicClosure ℚ)) : IsDominant (barPt A) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap A.subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
  exact bot_le

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    (∀ x : JH M H, x ∈ O.finPts m ↔
      x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧ ExtendsToPlace A Λ.σA (O.pts x)) ∧
    (∀ s : SchemeHomOver Λ.σA O.g, O.L.IsTorsionPoint Λ.σA m s →
      O.pts.symm (schemeHomOverComp (barPt A) Λ.hσA s) ∈ O.finPts m) ∧
    (∀ x ∈ O.finPts m, ∀ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 → O.L.IsTorsionPoint Λ.σA m s) ∧
    (∀ s : SchemeHomOver Λ.σA O.g, O.L.IsTorsionPoint Λ.σA m s →
      ∀ sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g, sκ.1 = resPt A ≫ s.1 → O.L.IsTorsionPoint (resPt A ≫ Λ.σA) m sκ) := by

  have hadd : ∀ x y : JH M H, O.pts (x + y) = O.L.mul _ (O.pts x) (O.pts y) := O.pts_add
  have hzero : O.pts 0 = O.L.one (genPt p) := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact eq_one_of_mul_self _ _ _ h.symm
  have hneg : ∀ x : JH M H, O.pts (-x) = O.L.inv _ (O.pts x) := by
    intro x
    letI := O.L.pointGroup (genPt p)
    apply eq_inv_of_mul_eq_one_left
    show O.L.mul _ (O.pts (-x)) (O.pts x) = O.L.one _
    rw [← hadd, neg_add_cancel, hzero]
  have hnsmul : ∀ (n : ℕ) (x : JH M H), O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
    intro n x
    induction n with
    | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, RelativeGroupLaw.nsmul_succ]

  have hext : ∀ x : JH M H, ExtendsToPlace A Λ.σA (O.pts x) ↔
      ∃ s : SchemeHomOver Λ.σA O.g, O.pts x = schemeHomOverComp (barPt A) Λ.hσA s := by
    intro x
    exact ⟨fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩, fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩⟩

  have hEadd : ∀ x y, ExtendsToPlace A Λ.σA (O.pts x) → ExtendsToPlace A Λ.σA (O.pts y) →
      ExtendsToPlace A Λ.σA (O.pts (x + y)) := by
    intro x y hx hy
    rw [hext] at hx hy ⊢
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    exact ⟨O.L.mul _ s s', by rw [hadd, hs, hs', ← O.L.mul_natural]⟩
  have hEneg : ∀ x, ExtendsToPlace A Λ.σA (O.pts x) → ExtendsToPlace A Λ.σA (O.pts (-x)) := by
    intro x hx
    rw [hext] at hx ⊢
    obtain ⟨s, hs⟩ := hx
    exact ⟨O.L.inv _ s, by rw [hneg, hs, inv_natural]⟩
  have hEzero : ExtendsToPlace A Λ.σA (O.pts 0) := by
    rw [hext]
    exact ⟨O.L.one _, by rw [hzero, O.L.one_natural]⟩

  have hi : ∀ x : JH M H, x ∈ O.finPts m ↔
      x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧ ExtendsToPlace A Λ.σA (O.pts x) := by
    intro x
    let S : AddSubgroup (JH M H) :=
      { carrier := {x | x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧ ExtendsToPlace A Λ.σA (O.pts x)}
        add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, hEadd a b ha.2 hb.2⟩
        zero_mem' := ⟨zero_mem _, hEzero⟩
        neg_mem' := fun {a} ha => ⟨neg_mem ha.1, hEneg a ha.2⟩ }
    change x ∈ AddSubgroup.closure (S : Set (JH M H)) ↔ x ∈ (S : Set (JH M H))
    rw [AddSubgroup.closure_eq]
    rfl

  have htors : ∀ x : JH M H, x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ↔ m • x = 0 := by
    intro x
    rw [Pic0.mem_torsion, natCast_zsmul]
  haveI := isDominant_barPt A
  haveI : IsSeparated O.g := O.separated
  refine ⟨hi, ?_, ?_, ?_⟩
  ·
    intro s hs
    rw [hi]
    refine ⟨?_, ⟨s, by rw [Equiv.apply_symm_apply]; rfl⟩⟩
    rw [htors, ← O.pts.injective.eq_iff, hnsmul, Equiv.apply_symm_apply, ← nsmul_natural,
      (RelativeGroupLaw.isTorsionPoint_def _ _ _ _).mp hs, O.L.one_natural, hzero]
  ·
    intro x hx s hs
    rw [hi] at hx
    have hx0 : m • x = 0 := (htors x).mp hx.1
    have hps : O.pts x = schemeHomOverComp (barPt A) Λ.hσA s := Subtype.ext hs

    have hgen : schemeHomOverComp (barPt A) Λ.hσA (O.L.nsmul _ m s) =
        schemeHomOverComp (barPt A) Λ.hσA (O.L.one _) := by
      rw [nsmul_natural, ← hps, ← hnsmul, hx0, hzero, O.L.one_natural]
    rw [RelativeGroupLaw.isTorsionPoint_def]
    apply Subtype.ext
    refine ext_of_isDominant_of_isSeparated O.g ?_ (barPt A) ?_
    · rw [(O.L.nsmul Λ.σA m s).2, (O.L.one Λ.σA).2]
    · exact congrArg Subtype.val hgen
  ·
    intro s hs sκ hsκ
    have hsκ' : sκ = schemeHomOverComp (resPt A) rfl s := Subtype.ext hsκ
    rw [RelativeGroupLaw.isTorsionPoint_def, hsκ', ← nsmul_natural,
      (RelativeGroupLaw.isTorsionPoint_def _ _ _ _).mp hs, O.L.one_natural]

end S_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt (solution)
