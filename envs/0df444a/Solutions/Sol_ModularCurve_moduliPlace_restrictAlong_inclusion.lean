-- Prove2me | solution 1 for ModularCurve.moduliPlace_restrictAlong_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f17178aa-4c87-5e59-a6f0-b65250cd2d33

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

noncomputable section

namespace P2MKcDegC6

universe u v

section CycSub

variable {A : Type*} [AddCommGroup A] {N : ℕ}

private theorem _root_.P2MKcDegC6.exists_generator (hN : N ≠ 0)
    (H : {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}) :
    ∃ g : A, addOrderOf g = N ∧ AddSubgroup.zmultiples g = H.1 := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
  have hfin : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hog : addOrderOf g = N := (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcard
  refine ⟨g.1, by rw [AddSubgroup.addOrderOf_coe, hog], ?_⟩
  have hle : AddSubgroup.zmultiples (g.1) ≤ H.1 := by
    rw [AddSubgroup.zmultiples_le]; exact g.2
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hog]

p2m_export "P2MKcDegC6" "exists_generator"

theorem eq_of_le_of_card_eq {H H' : AddSubgroup A} (hle : H ≤ H') (hH : Nat.card H = N)
    (hH' : Nat.card H' = N) (hN : N ≠ 0) : H = H' := by
  haveI : Finite H' := Nat.finite_of_card_ne_zero (by rw [hH']; exact hN)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hH, hH'])

theorem addOrderOf_div_nsmul {M : ℕ} (hMN : M ∣ N) (hN : N ≠ 0) {g : A} (hg : addOrderOf g = N) :
    addOrderOf ((N / M) • g) = M := by
  have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hMN (Nat.pos_of_ne_zero hN)
  have hq : 0 < N / M := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hMN) hM0
  rw [addOrderOf_nsmul' _ hq.ne', hg, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hMN),
    Nat.div_div_self hMN hN]

end CycSub

section VC

variable {L : Type*} [Field L] [DecidableEq L]

def vcInvHom (C : VariableChange L) (W : WeierstrassCurve.Affine L) :
    W.Point →+ (C • W).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun C W) (Point.vcInvFun_add C W)

@[scoped simp] theorem vcInvHom_apply (C : VariableChange L) (W : WeierstrassCurve.Affine L) (P : W.Point) :
    vcInvHom C W P = Point.vcInvFun C W P := rfl

theorem vcInvFun_nsmul (C : VariableChange L) (W : WeierstrassCurve.Affine L) (n : ℕ)
    (P : W.Point) : Point.vcInvFun C W (n • P) = n • Point.vcInvFun C W P := by
  rw [← vcInvHom_apply, map_nsmul, vcInvHom_apply]

end VC

section Lower

variable {L : Type u} {L' : Type v} [Field L] [Field L'] [DecidableEq L] [DecidableEq L']
  {N M : ℕ} [NeZero N]

def lowerPair (hMN : M ∣ N) (P : Gamma0Pair N L) : Gamma0Pair M L where
  toCurve := P.toCurve
  isElliptic := P.isElliptic
  gen := (N / M) • P.gen
  addOrderOf_gen := addOrderOf_div_nsmul hMN (NeZero.ne N) P.addOrderOf_gen

@[scoped simp] theorem lowerPair_toCurve (hMN : M ∣ N) (P : Gamma0Pair N L) :
    (lowerPair hMN P).toCurve = P.toCurve := rfl

@[scoped simp] theorem lowerPair_gen (hMN : M ∣ N) (P : Gamma0Pair N L) :
    (lowerPair hMN P).gen = (N / M) • P.gen := rfl

theorem lowerPair_step (hMN : M ∣ N) {P Q : Gamma0Pair N L} (h : Gamma0Pair.Step P Q) :
    Gamma0Pair.Step (lowerPair hMN P) (lowerPair hMN Q) := by
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨WP, hEP, gP, hgP⟩ := P
  obtain ⟨WQ, hEQ, gQ, hgQ⟩ := Q
  change γ • WP = WQ at hγ
  subst hγ
  change HEq gQ (k • Point.vcInvFun γ WP.toAffine gP) at hgen
  have hgen' : gQ = k • Point.vcInvFun γ WP.toAffine gP := eq_of_heq hgen
  refine ⟨γ, rfl, k, hk.coprime_dvd_right hMN, ?_⟩
  show HEq ((N / M) • gQ) (k • Point.vcInvFun γ WP.toAffine ((N / M) • gP))
  rw [hgen', vcInvFun_nsmul, smul_smul, smul_smul, mul_comm]

def lower (hMN : M ∣ N) : ModuliPoint N L → ModuliPoint M L :=
  Quot.lift (fun P => (Quot.mk _ (lowerPair hMN P) : ModuliPoint M L))
    fun _ _ h => Quot.sound (lowerPair_step hMN h)

@[scoped simp] theorem lower_mk (hMN : M ∣ N) (P : Gamma0Pair N L) :
    lower hMN (Quot.mk _ P : ModuliPoint N L) = (Quot.mk _ (lowerPair hMN P) : ModuliPoint M L) :=
  rfl

theorem lower_map (hMN : M ∣ N) (σ : L →+* L') (x : ModuliPoint N L) :
    lower hMN (ModuliPoint.map σ x) = ModuliPoint.map σ (lower hMN x) := by
  induction x using Quot.ind with
  | _ P =>
    rw [ModuliPoint.map_mk, lower_mk, lower_mk, ModuliPoint.map_mk]
    congr 1
    exact Gamma0Pair.ext_heq rfl (heq_of_eq (WeierstrassCurve.mapPoint_nsmul σ (N / M) P.gen).symm)

end Lower

section Cusp

variable (K : Type u) [Field K] {N M : ℕ} [NeZero N] [NeZero M]

theorem restrictAlong_inclusion_qInftyPlaceMod (hMN : M ∣ N)
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral) :
    (qInftyPlaceMod K (jqModC_mem_full K N)).restrictAlong
        (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι =
      qInftyPlaceMod K (jqModC_mem_full K M) :=
  Place.ext (SetLike.ext fun _ => Iff.rfl)

end Cusp

section Datum

variable {K : Type u} [Field K] [DecidableEq K] {N M : ℕ} [NeZero N] [NeZero M]
  {x : ModuliPoint N K} {Ω : Type u} [Field Ω] [DecidableEq Ω] [Algebra K Ω]
  (D : ModuliTestDatum K N x Ω)

theorem map_res_mk_levelGen (hMN : M ∣ N) :
    letI := Classical.decEq (ResidueField D.W.toValuationSubring)
    ModuliPoint.map D.res
      (Quot.mk _ (⟨D.curve.map (residue D.W.toValuationSubring),
        ⟨isUnit_iff_ne_zero.mpr D.map_Δ_ne_zero⟩, reduceHom D.map_Δ_ne_zero ((N / M) • D.gen),
          D.addOrderOf_reduceHom_levelGen hMN⟩ :
            Gamma0Pair M (ResidueField D.W.toValuationSubring))) = lower hMN x := by
  letI := Classical.decEq (ResidueField D.W.toValuationSubring)
  obtain ⟨hord, hred⟩ := D.reduction
  have h1 : (⟨D.curve.map (residue D.W.toValuationSubring),
        ⟨isUnit_iff_ne_zero.mpr D.map_Δ_ne_zero⟩, reduceHom D.map_Δ_ne_zero ((N / M) • D.gen),
          D.addOrderOf_reduceHom_levelGen hMN⟩ :
            Gamma0Pair M (ResidueField D.W.toValuationSubring)) =
      lowerPair hMN ⟨D.curve.map (residue D.W.toValuationSubring),
          ⟨isUnit_iff_ne_zero.mpr D.map_Δ_ne_zero⟩, reduceHom D.map_Δ_ne_zero D.gen, hord⟩ :=
    Gamma0Pair.ext_heq rfl (heq_of_eq (map_nsmul (reduceHom D.map_Δ_ne_zero) (N / M) D.gen))
  rw [h1, ← lower_mk, ← lower_map, hred]

end Datum

section Main

variable (K : Type u) [Field K] [DecidableEq K] (N M : ℕ) [NeZero N] [NeZero M]

theorem main (hMN : M ∣ N)
    (hex : ∀ x : ModuliPoint N K, ∃ v, IsModuliPlaceOf K N x v)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K (modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral)
    (E : WeierstrassCurve K)
    (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N})
    (C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
    (hCC' : ∀ T ∈ C.1, (N / M) • T ∈ C'.1) :
    (moduliPlace K N E C.1).restrictAlong
        (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι =
      moduliPlace K M E C'.1 := by
  by_cases hE : E.IsElliptic
  ·
    obtain ⟨g, hg, hgC⟩ := exists_generator (NeZero.ne N) C
    have hg' : addOrderOf ((N / M) • g) = M := addOrderOf_div_nsmul hMN (NeZero.ne N) hg
    have hgC' : AddSubgroup.zmultiples ((N / M) • g) = C'.1 :=
      eq_of_le_of_card_eq
        (AddSubgroup.zmultiples_le.mpr (hCC' g (hgC ▸ AddSubgroup.mem_zmultiples g)))
        (by rw [Nat.card_zmultiples, hg']) C'.2.2 (NeZero.ne M)
    rw [← hgC, ← hgC', moduliPlace_zmultiples K N E g hg, moduliPlace_zmultiples K M E _ hg']

    obtain ⟨Ω, _, _, _, D, hD⟩ :=
      isModuliPlaceOf_moduliPlaceOfPoint K N (hex (Quot.mk _ (⟨E, hE, g, hg⟩ : Gamma0Pair N K)))

    have h := D.isModuliPlaceOf_restrictAlong_inclusion hMN
      (Quot.mk _ (⟨E, hE, (N / M) • g, hg'⟩ : Gamma0Pair M K)) (map_res_mk_levelGen D hMN) hι hD
    exact (moduliPlaceOfPoint_eq_of_forall_eq K M (huniq _) h).symm
  · rw [moduliPlace_of_not_isElliptic K N hE, moduliPlace_of_not_isElliptic K M hE]
    exact restrictAlong_inclusion_qInftyPlaceMod K hMN hι

end Main

end P2MKcDegC6
p2m_reactivate "P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion.P2MKcDegC6"

universe u in

theorem solution
    (K : Type u) [Field K] [DecidableEq K] (N M : ℕ) [NeZero N] [NeZero M] (hMN : M ∣ N)
    (hex : ∀ x : ModuliPoint N K, ∃ v, IsModuliPlaceOf K N x v)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K ↥(modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral)
    (E : WeierstrassCurve K)
    (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N})
    (C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
    (hCC' : ∀ T ∈ C.1, (N / M) • T ∈ C'.1) :
    (moduliPlace K N E C.1).restrictAlong
        (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι =
      moduliPlace K M E C'.1 :=
  P2MKcDegC6.main K N M hMN hex huniq hι E C C' hCC'

end
p2m_reactivate "P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion.P2MKcDegC6"

end S_ModularCurve_moduliPlace_restrictAlong_inclusion
end P2MW
export P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion (solution)
