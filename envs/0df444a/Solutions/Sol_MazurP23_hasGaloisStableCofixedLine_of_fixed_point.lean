-- Prove2me | solution 1 for MazurP23.hasGaloisStableCofixedLine_of_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:32:58.201205+00:00
-- url     : https://prove2.me/submissions/7d4506b4-d9fe-4613-be39-21d7b567a445

import Mathlib
import Theorems.Thm_MazurP23_card_zeroComponent_prime_torsion
import Theorems.Thm_MazurP23_det_galoisRep_eq_cycloExp
import Theorems.Thm_MazurP23_inertia_smul_eq_self_of_not_dvd_discr
import Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_goodReduction
import Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_isOpen_torsionBy_fixingSubgroup
import Theorems.Thm_ExtCitation_extVanishingCts_of_three_le
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_AdmissibleExtension
import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23

/-- An endomorphism fixing a line acts on the one-dimensional quotient by its determinant. -/
private theorem sub_det_smul_mem_of_fixed_line
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : Module.finrank F V = 2) (f : V →ₗ[F] V)
    (C : Submodule F V) (hC : Module.finrank F C = 1)
    (hfix : ∀ x ∈ C, f x = x) (x : V) :
    f x - LinearMap.det f • x ∈ C := by
  have : FiniteDimensional F V := Module.finite_of_finrank_pos (by omega)
  have hstable : C ≤ C.comap f := by
    intro y hy
    change f y ∈ C
    rw [hfix y hy]
    exact hy
  have hrestrict : f.restrict hstable = LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact hfix y y.property
  have hquotient : Module.finrank F (V ⧸ C) = 1 := by
    have hd := C.finrank_quotient_add_finrank
    omega
  obtain ⟨a, ha, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hquotient (C.mapQ C f hstable)
  have hdet : LinearMap.det f = a := by
    rw [LinearMap.det_eq_det_mul_det C f hstable, hrestrict, ha]
    simp [LinearMap.det_smul, hquotient]
  rw [← C.ker_mkQ, LinearMap.mem_ker]
  change C.mkQ (f x - LinearMap.det f • x) = 0
  rw [map_sub, map_smul, hdet]
  have haction := congrArg (fun g : (V ⧸ C) →ₗ[F] (V ⧸ C) => g (C.mkQ x)) ha
  simpa using sub_eq_zero.mpr haction

/-- A fixed prime-order point and the local hypotheses yield a cofixed line by splitting
the extension of the cyclotomic quotient by the line spanned by the point. -/
theorem _root_.solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    (h2Δ : (2:ℤ) ∣ W.Δ) (h2c₄ : ¬ (2:ℤ) ∣ W.c₄)
    (h3Δ : (3:ℤ) ∣ W.Δ) (h3c₄ : ¬ (3:ℤ) ∣ W.c₄)
    (hloc : ∀ q : ℕ, q.Prime → q ≠ p →
      ¬ (q : ℤ) ∣ W.Δ ∨ ((q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄) ∨
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y)
    (hpat : (¬ (p : ℤ) ∣ W.Δ ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ (x y : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          p • (Point.some x y h) = 0 ∧ x ∈ A)
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄))
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p)
    (h2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ¬ W.InZeroComponentAt A Q)
    (h3 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 → ¬ W.InZeroComponentAt A Q) :
    HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : (W.map (Int.castRingHom ℚ)).IsElliptic := by
    apply (WeierstrassCurve.isElliptic_iff _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [WeierstrassCurve.map_Δ, eq_intCast]
    exact_mod_cast hΔ
  let V := Submodule.torsionBy ℤ
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (p : ℤ)
  have htor (v : V) : p • v.val = 0 := by
    have hv : (p : ℤ) • v.val = 0 := v.property
    simpa only [natCast_zsmul] using hv
  have hcard : Nat.card V = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ)
      (W.map (Int.castRingHom ℚ)) (Nat.cast_ne_zero.mpr hp.ne_zero)
  have : Finite V := Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero 2 hp.ne_zero))
  have hdim : Module.finrank (ZMod p) V = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcard, Nat.card_zmod] at hh
    exact (Nat.pow_right_injective hp.two_le hh).symm
  have hQtor : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  let q₀ : V := ⟨Q, by
    change (p : ℤ) • Q = 0
    simpa only [natCast_zsmul] using hQtor⟩
  have hq₀ : q₀ ≠ 0 := by
    intro hh
    have hz : Q = 0 := congrArg Subtype.val hh
    simpa [hz] using hQord.trans_ne (by omega : p ≠ 1)
  let C : Submodule (ZMod p) V := Submodule.span (ZMod p) {q₀}
  have hqdim : Module.finrank (ZMod p) C = 1 := finrank_span_singleton hq₀
  have hCcard : Nat.card C = p := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hqdim, pow_one]
  have hCfix (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : V)
      (hx : x ∈ C) : σ • x = x := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_comm σ a]
    congr 1
    exact Subtype.ext (hQfix σ)
  have hCbot : C ≠ ⊥ := by
    intro h
    have hh : Module.finrank (ZMod p) C = 0 := by rw [h]; simp
    omega
  have hCtop : C ≠ ⊤ := by
    intro h
    have hh : Module.finrank (ZMod p) C = 2 := by rw [h]; simpa using hdim
    omega
  have hcompl (M : Submodule (ZMod p) V) (hm : Nat.card M = p) (hne : C ≠ M) :
      IsCompl C M := by
    have hmdim : Module.finrank (ZMod p) M = 1 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
      rw [hm, Nat.card_zmod] at hh
      exact (Nat.pow_right_injective hp.two_le ((pow_one p).trans hh)).symm
    apply (Submodule.isCompl_iff_disjoint C M (by omega)).mpr
    exact (Submodule.isAtom_iff_finrank_eq_one.mpr hqdim).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.mpr hmdim) hne
  have hquot (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : V) :
      σ • x - (ExtCitation.cycloExp p σ : ZMod p) • x ∈ C := by
    have hh := sub_det_smul_mem_of_fixed_line hdim
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      C hqdim (hCfix σ) x
    rwa [det_galoisRep_eq_cycloExp W p hΔ σ] at hh
  have hadm : ExtCitation.IsAdmissibleExtensionCts p V C := by
    refine {
      stable := fun σ x hx => by rw [hCfix σ x hx]; exact hx
      fixed_sub := hCfix
      cyclo_quot := hquot
      card_sub := hCcard
      card_total := hcard
      unramified_outside := ?_
      locally_split := ?_
      open_kernel := WeierstrassCurve.isOpen_torsionBy_fixingSubgroup W p hΔ hp.pos }
    · intro ℓ hℓ hℓp A hA σ hσ x
      rcases hloc ℓ hℓ hℓp with hgood | ⟨hℓΔ, hℓc₄⟩ | htriv
      · exact Subtype.ext (inertia_smul_eq_self_of_not_dvd_discr W hℓ hgood A hA hσ
          (fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)) x.val (htor x))
      · have hp' : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        have hout := WeierstrassCurve.mazurStepThree_not_inZeroComponentAt hp hp' W hΔ Q
          hQfix hQord h2Δ h2c₄ h2 h3Δ h3c₄ h3 hℓ hℓp hℓΔ hℓc₄ A hA
        obtain ⟨M, hMiff, -, hMfix⟩ :=
          WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
            W hℓ hΔ hℓΔ hℓc₄ A hA hp
        have hm : Nat.card M = p := by
          have e : M ≃ {z : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
              p • z = 0 ∧ W.InZeroComponentAt A z} := {
            toFun := fun m => ⟨m.val.val, htor m.val, (hMiff m.val).mp m.property⟩
            invFun := fun z => ⟨⟨z.val, by
              change (p : ℤ) • z.val = 0
              simpa only [natCast_zsmul] using z.property.1⟩,
              (hMiff _).mpr z.property.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
          rw [Nat.card_congr e]
          exact card_zeroComponent_prime_torsion W hℓ hΔ hℓΔ hℓc₄ A hA p
            (Ne.symm hℓp) hcard
        have hCM := hcompl M hm (by
          intro heq
          have hqmem : q₀ ∈ M := heq ▸ Submodule.subset_span (Set.mem_singleton q₀)
          exact hout ((hMiff q₀).mp hqmem))
        have hx : x ∈ C ⊔ M := hCM.sup_eq_top ▸ Submodule.mem_top
        obtain ⟨c, hc, m, hm, rfl⟩ := Submodule.mem_sup.mp hx
        rw [smul_add, hCfix σ c hc, hMfix (Ne.symm hℓp) σ hσ m hm]
      · apply Subtype.ext
        exact htriv A hA σ hσ 1 x.val (by rw [pow_one]; exact htor x)
    · intro A hA
      obtain ⟨F, hFtor, hFcard, hFstable, hFabsorb⟩ :
          ∃ F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
            (∀ y ∈ F, p • y = 0) ∧ Nat.card F = p ∧
            (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ y ∈ F, σ • y ∈ F) ∧
            (∀ σ ∈ A.inertiaSubgroupIn ℚ,
              ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
                p • y = 0 → σ • y - y ∈ F) := by
        rcases hpat with ⟨hgood, hord⟩ | ⟨hbad, hmult⟩
        · obtain ⟨F, hF, hc, hs, ha⟩ :=
            WeierstrassCurve.exists_atP_filtration_of_goodReduction W p hp2 hgood A hA
              (hord A hA) 1 (by omega)
          refine ⟨F, ?_, by simpa using hc, hs, ?_⟩
          · intro y hy; simpa using ((hF y).mp hy).1
          · simpa using ha
        · obtain ⟨F, hF, hc, hs, ha⟩ :=
            WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction W p hp2 hΔ
              hbad hmult A hA 1 (by omega)
          refine ⟨F, ?_, by simpa using hc, hs, ?_⟩
          · intro y hy; simpa using ((hF y).mp hy).1
          · simpa using ha
      let M : Submodule (ZMod p) V := {
        carrier := {v | v.val ∈ F}
        zero_mem' := F.zero_mem
        add_mem' := fun hx hy => F.add_mem hx hy
        smul_mem' := by
          intro a x hx
          change ((a • x : V) : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) ∈ F
          have he : a • x = a.val • x := by
            simpa only [ZMod.natCast_zmod_val] using
              (Nat.cast_smul_eq_nsmul (ZMod p) a.val x)
          rw [he]
          exact F.nsmul_mem hx a.val }
      have hm : Nat.card M = p := by
        let e : M ≃ F := {
          toFun := fun x => ⟨x.val.val, x.property⟩
          invFun := fun x => ⟨⟨x.val, by
            change (p : ℤ) • x.val = 0
            simpa only [natCast_zsmul] using hFtor x.val x.property⟩,
            x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
        exact (Nat.card_congr e).trans hFcard
      refine ⟨M, fun σ hσ x hx => hFstable σ hσ x.val hx, hcompl M hm ?_⟩
      intro hCM
      obtain ⟨σ, hσ, hdet⟩ := WeierstrassCurve.det_galoisRep_surjOn_inertia W p hΔ A hA (-1)
      have hdet' : LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ) = (-1 : ZMod p) := by
        simpa using hdet
      have hall (x : V) : (2 : ZMod p) • x ∈ C := by
        have ha : σ • x - x ∈ C := hCM ▸ hFabsorb σ hσ x.val (htor x)
        have hb := sub_det_smul_mem_of_fixed_line hdim
          (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
            (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
          C hqdim (hCfix σ) x
        rw [hdet'] at hb
        change σ • x - (-1 : ZMod p) • x ∈ C at hb
        have hc := C.sub_mem hb ha
        convert hc using 1 <;> simp only [_root_.neg_smul, one_smul, two_smul] <;> abel
      have htwo : (2 : ZMod p) ≠ 0 := by
        intro hzero
        have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
        have := Nat.le_of_dvd (by omega : 0 < 2) hdiv
        omega
      apply hCtop
      apply top_unique
      intro x _
      have hh := C.smul_mem (2 : ZMod p)⁻¹ (hall x)
      simpa [smul_smul, htwo] using hh
  obtain ⟨N, hNstable, hCN⟩ := ExtCitation.extVanishingCts_of_three_le (by omega : 3 ≤ p) V C hadm
  refine ⟨N, hNstable, ?_, ?_, ?_⟩
  · intro hn
    exact hCtop (by simpa [hn] using hCN.sup_eq_top)
  · intro hn
    exact hCbot (by simpa [hn] using hCN.inf_eq_bot)
  · intro σ x
    have hx : x ∈ C ⊔ N := hCN.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨c, hc, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
    have hh := N.sub_mem (hNstable σ n hn) hn
    simpa only [smul_add, hCfix σ c hc, add_sub_add_left_eq_sub] using hh

end MazurP23
