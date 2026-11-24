-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:49.851799+00:00
-- url     : https://prove2.me/submissions/8a0d4ec8-ef98-440d-9e3c-9b6e828a01b7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_ha_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_tm_actW
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_mem_latV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_Lv_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_eventually_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_eventually_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_act_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_act_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_projV_projFin
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_map_eqs
import Theorems.Thm_GlobalTheory_T_adelic_tuple_projections
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (pinf : HA (AF F) σ J →* HA (Ainf F) σ J) (p : ∀ v : HeightOneSpectrum (𝓞 F), HA (AF F) σ J →* HA (Fv F v) σ J), (∀ (n : ℕ) (h : HA (AF F) σ J) (X : (Fin n → Fin M → AF F ⊗[F] E)), projInf (actW (AF F) σ J h X) = actW (Ainf F) σ J (pinf h) (projInf X) ∧ ∀ v, projV v (projFin (actW (AF F) σ J h X)) = actW (Fv F v) σ J (p v h) (projV v (projFin X))) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J), ∀ᶠ v in Filter.cofinite, ∀ (n : ℕ) (X : (Fin n → Fin M → Fv F v ⊗[F] E)), actW (Fv F v) σ J (p v h) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ginf : HA (Ainf F) σ J) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), ∃ h : HA (AF F) σ J, pinf h = ginf ∧ (∀ v ∈ S, p v h = g v) ∧ ∀ v, v ∉ S → p v h = 1 := by
  intro F E _ _ _ _ _ σ hCM M J _
  refine ⟨hMap σ J (fstA F), fun v => hMap σ J (evA v), ?_, ?_, ?_⟩
  · intro n h X
    refine ⟨tm_actW σ J (fstA F) h X, fun v => ?_⟩
    rw [projV_projFin, projV_projFin]
    exact tm_actW σ J (evA v) h X
  · intro d b h
    have entries : ∀ h : HA (AF F) σ J, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
        ((HA.mat (Fv F v) σ J (hMap σ J (evA v) h) : GL _ _) :
          Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ Lv b v := by
      intro h
      obtain ⟨-, -, -, -, -, ev, -, -, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM d b M M
      filter_upwards [ev (projFin (fun a i =>
        ((HA.mat (AF F) σ J h : GL _ _) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) a i))] with v hv i j
      rw [projV_projFin] at hv
      exact (mem_latV b v _).1 hv i j
    filter_upwards [eventually_mul b, entries h, entries h⁻¹] with v hm h1 h2 n X
    constructor
    · intro hX
      rw [← act_inv (Fv F v) σ J (hMap σ J (evA v) h) X, ← map_inv]
      exact act_mem b v hm _ h2 _ hX
    · intro hX
      exact act_mem b v hm _ h1 _ hX
  · intro S ginf g
    classical
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
    obtain ⟨-, -, -, -, -, -, inj, glue, -⟩ :=
      GlobalTheory.T.adelic_tuple_projections F E σ hCM _ (Module.finBasis F E) M M
    have injM : ∀ A B : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
        A.map (tm E (fstA F)) = B.map (tm E (fstA F)) →
        (∀ v : HeightOneSpectrum (𝓞 F), A.map (tm E (evA v)) = B.map (tm E (evA v))) → A = B := by
      intro A B h1 h2
      refine inj A B h1 fun v => ?_
      exact (projV_projFin v A).trans ((h2 v).trans (projV_projFin v B).symm)
    have oneLat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        (fun a i => (1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) a i) ∈
          (latV (Module.finBasis F E) v : Set (Fin M → Fin M → Fv F v ⊗[F] E)) := by
      filter_upwards [eventually_one (Module.finBasis F E)] with v hv
      refine (mem_latV _ v _).2 fun a i => ?_
      by_cases e : a = i
      · subst e; simpa using hv
      · simpa [Matrix.one_apply_ne e] using Lv_zero (Module.finBasis F E) v
    have glueM : ∀ (ginf : HA (Ainf F) σ J) (G : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
        (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, G v = 1) →
        ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
          X.map (tm E (fstA F)) =
            ((HA.mat (Ainf F) σ J ginf : GL _ _) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) ∧
          ∀ v : HeightOneSpectrum (𝓞 F), X.map (tm E (evA v)) =
            ((HA.mat (Fv F v) σ J (G v) : GL _ _) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) := by
      intro ginf G hG
      obtain ⟨X, hXi, hXv⟩ := glue
        (fun a i => ((HA.mat (Ainf F) σ J ginf : GL _ _) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) a i)
        (fun v a i => ((HA.mat (Fv F v) σ J (G v) : GL _ _) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) a i)
        (by
          filter_upwards [hG, oneLat] with v h1 h2
          rw [h1]
          exact h2)
      exact ⟨X, hXi, fun v => (projV_projFin v X).symm.trans (hXv v)⟩
    let G : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J := fun v => if v ∈ S then g v else 1
    have hS : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, G v = 1 := by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      exact if_neg hv
    obtain ⟨X, mi, mv⟩ := glueM ginf G hS
    obtain ⟨X', mi', mv'⟩ := glueM ginf⁻¹ (fun v => (G v)⁻¹) (by
      filter_upwards [hS] with v hv
      rw [hv, inv_one])
    have e1 : X * X' = 1 :=
      injM _ _ (map_eqs σ J _ _ _ ginf mi mi').1 fun v => (map_eqs σ J _ _ _ (G v) (mv v) (mv' v)).1
    have e2 : cT (sigR (AF F) σ) X * JR (AF F) J * X = JR (AF F) J :=
      injM _ _ (map_eqs σ J _ _ _ ginf mi mi').2 fun v => (map_eqs σ J _ _ _ (G v) (mv v) (mv' v)).2
    let hh : HA (AF F) σ J := (⟨⟨X, X', e1, mul_eq_one_comm.1 e1⟩, e2⟩ : HR (AF F) σ J)
    refine ⟨hh, ha_ext σ J mi, fun v hv => ha_ext σ J ?_, fun v hv => ha_ext σ J ?_⟩
    · have e : G v = g v := if_pos hv
      have m := mv v
      rw [e] at m
      exact m
    · have e : G v = 1 := if_neg hv
      have m := mv v
      rw [e] at m
      exact m
end GlobalTheory.CompanionTheory.SW.HProj
