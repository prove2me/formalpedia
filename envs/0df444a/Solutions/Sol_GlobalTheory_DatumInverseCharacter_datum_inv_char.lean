-- Prove2me | solution 1 for GlobalTheory.DatumInverseCharacter.datum_inv_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:50:40.992438+00:00
-- url     : https://prove2.me/submissions/60207e5e-e362-45a1-963b-da6681299c7d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_right
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_left
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_exists_adjoint
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_modN_of_dvd
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_of_modN
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_mem_of_modN
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_exists_quot_equiv
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_zpow_congr
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_root_pow
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_cHalf_mem
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_cSep_mem
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_qRep_spec
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_levRep_spec
import Theorems.Thm_GlobalTheory_DatumInverseCharacter_half_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DatumInverseCharacter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
set_option maxHeartbeats 1000000
namespace GlobalTheory.DatumInverseCharacter
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → Nat.Coprime d.pd l.M → d.l₂.Mb = l.Mb * d.I → d.I ⊔ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → l.Dvd d.l₂ → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, g.InGam l d.l₂ → ∃ (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂), (∀ a : Dw.La, (Submodule.Quotient.mk (g.f d.l₂.M a) : LaI Xo c d) = kI (Submodule.Quotient.mk a)) ∧ (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), d.w x0 (fun b => σq.symm (q b)) = d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.w x0 q := by
  intro E _ _ _ H Dw l Xo c n d hM hcop hb hsup hdvd ph ψ x₀ hpin g hg
  obtain ⟨-, hgM, -⟩ := hg
  have hI := half_prod hM hb
  have hpdII : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self _
  have hpdI : (d.pd : 𝓞 E) ∈ d.I :=
    (Ideal.mul_le_left : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.I) hpdII
  have hpdJ : (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) :=
    (Ideal.mul_le_right : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) hpdII
  have hM₂I : (d.l₂.M : 𝓞 E) ∈ d.I := by
    rw [hM, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hpdI
  have hM₂J : (d.l₂.M : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [hM, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hpdJ
  have hM₂B : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb := by
    have : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ d.l₂.Mb) this
  have hMB : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) this
  have hM₂pos : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hMpos : 0 < l.M := by have := l.three_le; omega
  have hpdpos : 0 < d.pd := by
    rcases Nat.eq_zero_or_pos d.pd with h0 | h0
    · rw [h0, Nat.mul_zero] at hM
      have := d.l₂.three_le
      omega
    · exact h0
  obtain ⟨G, hG⟩ := g.inv d.l₂.M hM₂pos
  obtain ⟨kI, hkI⟩ := exists_quot_equiv Dw hM₂I (g.f d.l₂.M) G hG
  obtain ⟨k₂, hk₂⟩ := exists_quot_equiv Dw hM₂B (g.f d.l₂.M) G hG
  obtain ⟨F', hF'⟩ := exists_adjoint Dw (g.f d.l₂.M)
  obtain ⟨G', hG'⟩ := exists_adjoint Dw G
  have hGF' : ∀ a, Dw.ModN d.l₂.M (G' (F' a) - a) ∧ Dw.ModN d.l₂.M (F' (G' a) - a) := by
    intro a
    constructor
    · refine modN_of_dvd Dw hM₂pos fun v => ?_
      rw [map_sub, LinearMap.sub_apply, hG', hF', ← map_sub]
      exact dvd_of_modN Dw a (hG v).2
    · refine modN_of_dvd Dw hM₂pos fun v => ?_
      rw [map_sub, LinearMap.sub_apply, hF', hG', ← map_sub]
      exact dvd_of_modN Dw a (hG v).1
  obtain ⟨kst, hkst⟩ := exists_quot_equiv Dw hM₂J F' G' hGF'
  have hle₂ : d.l₂.Mb ≤ l.Mb := by
    rw [hb]
    exact Ideal.mul_le_left
  have hle₂I : d.l₂.Mb ≤ d.I := by
    rw [hb]
    exact Ideal.mul_le_right
  have hrep : ∀ y : LevQ Dw d.l₂, g.f d.l₂.M (levRep (k₂.symm y)) - levRep y ∈
      (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro y
    apply (Submodule.Quotient.eq _).1
    rw [← hk₂, levRep_spec, levRep_spec, LinearEquiv.apply_symm_apply]
  have hdiffL : ∀ y : LevQ Dw d.l₂, levRep (k₂.symm y) - levRep y ∈
      (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro y
    have e1 : g.f d.l₂.M (levRep (k₂.symm y)) - levRep (k₂.symm y) ∈
        (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have t := g.tower l.M d.pd hMpos hpdpos (levRep (k₂.symm y))
      rw [← hM] at t
      rw [← sub_add_sub_cancel (g.f d.l₂.M (levRep (k₂.symm y))) (g.f l.M (levRep (k₂.symm y)))
        (levRep (k₂.symm y))]
      exact add_mem (mem_of_modN Dw hMB t) (hgM _)
    have e2 := Submodule.smul_mono_left hle₂ (hrep y)
    rw [show levRep (k₂.symm y) - levRep y = (g.f d.l₂.M (levRep (k₂.symm y)) - levRep y) -
      (g.f d.l₂.M (levRep (k₂.symm y)) - levRep (k₂.symm y)) by abel]
    exact sub_mem e2 e1
  have hz : zetaM c ^ l.M = 1 := by
    unfold zetaM
    exact root_pow c dvd_rfl
  have hpair : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂),
      zetaM c ^ pairL (l := l) x0 (fun b => levRep (k₂.symm (q b))) =
        zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) := by
    intro x0 q
    apply zpow_congr hMpos hz
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro b _
    rw [← map_sub, ← smul_sub]
    exact dvd_right Dw l.prod (cSep_mem l) (x0 b) (hdiffL (q b))
  have hp := hpin
  unfold DeltaDat.PhiPin at hp
  obtain ⟨-, -, hrule, -, -, hsum⟩ := hp
  have hcompat : ∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
      Dw.EF u (cHalf H d.I • qRep (kI (Submodule.Quotient.mk v)))) := by
    intro u v
    have m1 : qRep (kst (Submodule.Quotient.mk u)) - F' u ∈
        (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
      apply (Submodule.Quotient.eq _).1
      rw [qRep_spec, hkst]
    have m2 : g.f d.l₂.M v - qRep (kI (Submodule.Quotient.mk v)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := by
      apply (Submodule.Quotient.eq _).1
      rw [qRep_spec, hkI]
    have key : Dw.EF (F' u) (cHalf H d.I • v) = Dw.EF u (cHalf H d.I • g.f d.l₂.M v) := by
      rw [hF', map_smul]
    have eq : Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
        Dw.EF u (cHalf H d.I • qRep (kI (Submodule.Quotient.mk v))) =
        Dw.EF (qRep (kst (Submodule.Quotient.mk u)) - F' u) (cHalf H d.I • v) +
        Dw.EF u (cHalf H d.I • (g.f d.l₂.M v - qRep (kI (Submodule.Quotient.mk v)))) := by
      rw [map_sub, LinearMap.sub_apply, smul_sub, map_sub (Dw.EF u), key]
      ring
    rw [eq]
    exact dvd_add (dvd_left Dw hI (cHalf_mem d.I) v m1) (dvd_right Dw hI (cHalf_mem d.I) u m2)
  have hphi : ∀ q : Fin n → LevQ Dw d.l₂, d.eF (d.φδ (fun b => k₂.symm (q b))) =
      d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (d.φδ q) := by
    intro q
    rw [hsum, hsum, mul_finsum, ← finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => kst.toEquiv)]
    have hΦ : ∀ x : Fin n → LaJ Xo c d,
        (Equiv.piCongrRight fun _ : Fin n => kst.toEquiv) x = fun b => kst (x b) := fun x => rfl
    apply finsum_congr
    intro x
    rw [hΦ]
    have hZ : ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (kst (x b))) (cHalf H d.I • levRep (k₂.symm (q b)))) =
        ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b))) := by
      apply zpow_congr hpdpos (root_pow d.c₂ (Dvd.intro_left _ hM.symm))
      rw [← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro b _
      have hu : kst (x b) = kst (Submodule.Quotient.mk (qRep (x b))) := by rw [qRep_spec]
      have m3 : qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) - levRep (q b) ∈
          (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := by
        have a1 : qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) -
            g.f d.l₂.M (levRep (k₂.symm (q b))) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := by
          apply (Submodule.Quotient.eq _).1
          rw [qRep_spec, hkI]
        rw [← sub_add_sub_cancel _ (g.f d.l₂.M (levRep (k₂.symm (q b)))) _]
        exact add_mem a1 (Submodule.smul_mono_left hle₂I (hrep (q b)))
      rw [hu]
      have eq : Dw.EF (qRep (kst (Submodule.Quotient.mk (qRep (x b))))) (cHalf H d.I • levRep (k₂.symm (q b))) -
          Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)) =
          (Dw.EF (qRep (kst (Submodule.Quotient.mk (qRep (x b))))) (cHalf H d.I • levRep (k₂.symm (q b))) -
            Dw.EF (qRep (x b)) (cHalf H d.I • qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))))) +
          Dw.EF (qRep (x b)) (cHalf H d.I •
            (qRep (kI (Submodule.Quotient.mk (levRep (k₂.symm (q b))))) - levRep (q b))) := by
        rw [smul_sub, map_sub]
        ring
      rw [eq]
      exact dvd_add (hcompat _ _) (dvd_right Dw hI (cHalf_mem d.I) _ m3)
    rw [hrule kI kst hcompat x, map_mul, _root_.mul_assoc, hZ]
  refine ⟨kI, k₂.toEquiv, fun a => (hkI a).symm, fun a => hk₂ a, ?_⟩
  intro x0 q
  show d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (k₂.symm (q b))) * d.φδ (fun b => k₂.symm (q b))) =
    d.eF (((ψ kI)⁻¹ : c.Fˣ) : c.F) * d.eF (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b)) * d.φδ q)
  rw [map_mul, map_mul, hpair x0 q, hphi q]
  ring
end GlobalTheory.DatumInverseCharacter
