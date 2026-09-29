-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a429ab7e-90a7-5767-a6b8-7709dadaf8ca

import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open UnramifiedWhittaker NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal

namespace Ws23PosVol

open UnramifiedWhittaker NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev AA : Type := AdeleRing (𝓞 ℚ) ℚ

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem localAt_placeEmbed_self (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ v (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne (x : GL (Fin 2) (v.adicCompletion ℚ)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem placeEmbed_mem_fin (x : GL (Fin 2) (v.adicCompletion ℚ)) : placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact AdelicDock.glArch_finEmbed _ _ _

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 a) = unipotentGL2 (f a) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((unipotentGL2 a : Matrix (Fin 2) (Fin 2) A) i j) = (unipotentGL2 (f a) : Matrix (Fin 2) (Fin 2) B) i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

theorem det_unipotentGL2 {A : Type*} [CommRing A] (a : A) : Matrix.GeneralLinearGroup.det (unipotentGL2 a) = 1 :=
  Units.ext (by simp [Matrix.det_fin_two, unipotentGL2_coe])

noncomputable def uniAt (x : v.adicCompletion ℚ) : G2 :=
  unipotentGL2 (((0 : InfiniteAdeleRing ℚ), AdelicDock.splice (𝓞 ℚ) ℚ v 0 x) : AA)

theorem localAt_apply (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) (i j : Fin 2) :
    (localAt ℚ w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j = ((g : Matrix (Fin 2) (Fin 2) AA) i j).2 w := rfl

theorem localAt_eq_map (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    localAt ℚ w g = Matrix.GeneralLinearGroup.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rfl

theorem glArch_eq_map (g : G2) :
    AdelicLevel.glArch (𝓞 ℚ) ℚ g = Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) g := rfl

theorem localAt_uniAt_self (x : v.adicCompletion ℚ) : localAt ℚ v (uniAt v x) = unipotentGL2 x := by
  rw [localAt_eq_map, uniAt, map_unipotentGL2]
  congr 1
  show (AdelicDock.splice (𝓞 ℚ) ℚ v 0 x) v = x
  exact AdelicDock.splice_apply_self _ _ _ _ _

theorem localAt_uniAt_of_ne (x : v.adicCompletion ℚ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    localAt ℚ w (uniAt v x) = 1 := by
  rw [localAt_eq_map, uniAt, map_unipotentGL2, ← unipotentGL2_zero]
  congr 1
  show (AdelicDock.splice (𝓞 ℚ) ℚ v 0 x) w = 0
  rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hw]
  rfl

theorem uniAt_mem_fin (x : v.adicCompletion ℚ) : uniAt v x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff, glArch_eq_map, uniAt, map_unipotentGL2, ← unipotentGL2_zero]
  rfl

theorem uniAt_mem_unip (x : v.adicCompletion ℚ) : uniAt v x ∈ adelicUnipotent ℚ :=
  ⟨Multiplicative.ofAdd _, rfl⟩

theorem det_uniAt (x : v.adicCompletion ℚ) : Matrix.GeneralLinearGroup.det (uniAt v x) = 1 :=
  det_unipotentGL2 _

theorem eventually_mem_localLevelOne (g : G2) :
    ∀ᶠ w in Filter.cofinite, localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤ := by
  have h1 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ((g : Matrix (Fin 2) (Fin 2) AA) i j).2 w ∈ w.adicCompletionIntegers ℚ :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) AA) i j).2.2
  have h2 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) AA) i j).2 w ∈ w.adicCompletionIntegers ℚ :=
    fun i j => (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) AA) i j).2.2
  have hall := (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h2 i j)
  refine hall.mono fun w hw => ?_
  have hint : ∀ {x : w.adicCompletion ℚ}, x ∈ w.adicCompletionIntegers ℚ → Valued.v x ≤ NumberField.AdelicLevel.idealBound (𝓞 ℚ) (⊤ : Ideal (𝓞 ℚ)) w :=
    fun hx => by rw [NumberField.AdelicLevel.idealBound_top]; exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
  exact ⟨⟨fun i j => hw.1 i j, hint (hw.1 1 0), hint (sub_mem (hw.1 1 1) (one_mem _))⟩,
    ⟨fun i j => hw.2 i j, hint (hw.2 1 0), hint (sub_mem (hw.2 1 1) (one_mem _))⟩⟩

theorem mem_range_unipotentGL2Hom_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    g ∈ (unipotentGL2Hom (R := R)).range ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, h00, h10, h11]

theorem mul_comm_of_mem_range_unipotentGL2Hom {R : Type*} [CommRing R] {a b : GL (Fin 2) R}
    (ha : a ∈ (unipotentGL2Hom (R := R)).range) (hb : b ∈ (unipotentGL2Hom (R := R)).range) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem isClosed_range_unipotentGL2Hom {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T1Space R] : IsClosed (((unipotentGL2Hom (R := R)).range : Subgroup (GL (Fin 2) R)) : Set (GL (Fin 2) R)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have : (((unipotentGL2Hom (R := R)).range : Subgroup (GL (Fin 2) R)) : Set (GL (Fin 2) R)) =
      ((fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]
  rw [this]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

theorem localAt_mem_range_of_mem_adelicUnipotent (p : HeightOneSpectrum (𝓞 ℚ)) {g : AdelicGL2 (𝓞 ℚ) ℚ}
    (hg : g ∈ adelicUnipotent ℚ) :
    localAt ℚ p g ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range := by
  rw [mem_range_unipotentGL2Hom_iff]
  rw [show adelicUnipotent ℚ = (unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).range from rfl,
    mem_range_unipotentGL2Hom_iff] at hg
  have h : ∀ i j : Fin 2, (localAt ℚ p g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      (finAdeleEval (𝓞 ℚ) ℚ p) ((adeleFin (𝓞 ℚ) ℚ) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)) :=
    fun i j => rfl
  simp only [h, hg.1, hg.2.1, hg.2.2, map_one, map_zero, and_self]

theorem isLocalLevelOne_top_of_integral (v : HeightOneSpectrum (𝓞 ℚ)) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) : AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [NumberField.AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
  · rw [NumberField.AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      ((v.adicCompletionIntegers ℚ).sub_mem (hm 1 1) (v.adicCompletionIntegers ℚ).one_mem)

theorem mem_levelOne_top_of_forall_localAt (g : G2)
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤) :
    g ∈ levelOne (𝓞 ℚ) ℚ ⊤ := by
  rw [NumberField.AdelicLevel.mem_levelOne_iff, NumberField.AdelicLevel.mem_finiteLevelOne_iff]
  have hint : ∀ i j, ((glFin (𝓞 ℚ) ℚ g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun i j w => by
    have := ((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).1 (h w)).1.integral i j
    rw [localAt_apply] at this
    rw [glFin_apply]
    exact this
  have hint' : ∀ i j, (((glFin (𝓞 ℚ) ℚ g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := fun i j w => by
    have := ((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).1 (h w)).2.integral i j
    rw [← map_inv, localAt_apply] at this
    rw [← map_inv, glFin_apply]
    exact this
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ), (∀ i j, m i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) →
      NumberField.AdelicLevel.IsLevelOneMatrix (𝓞 ℚ) ℚ ⊤ m := fun m hm =>
    { integral := hm
      lowerLeft := fun w => (NumberField.AdelicLevel.idealBound_top w).symm ▸
        NumberField.AdelicLevel.valued_apply_le_one (hm 1 0) w
      lowerRight := fun w => (NumberField.AdelicLevel.idealBound_top w).symm ▸
        NumberField.AdelicLevel.valued_apply_le_one
          (NumberField.AdelicLevel.sub_mem_integralFiniteAdeles (hm 1 1)
            NumberField.AdelicLevel.one_mem_integralFiniteAdeles) w }
  exact ⟨key _ hint, key _ hint'⟩

theorem localAt_mem_localLevelOne_of_mem_levelOne_top {g : G2} (hg : g ∈ levelOne (𝓞 ℚ) ℚ ⊤)
    (w : HeightOneSpectrum (𝓞 ℚ)) : localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤ := by
  rw [NumberField.AdelicLevel.mem_levelOne_iff, NumberField.AdelicLevel.mem_finiteLevelOne_iff] at hg
  rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
  refine ⟨isLocalLevelOne_top_of_integral w _ fun i j => ?_,
    isLocalLevelOne_top_of_integral w _ fun i j => ?_⟩
  · have := hg.1.integral i j w
    rw [glFin_apply] at this
    rw [localAt_apply]
    exact this
  · have := hg.2.integral i j w
    rw [← map_inv, glFin_apply] at this
    rw [localAt_apply]
    exact this

theorem exists_unipotent_forall_localAt_mem :
    ∀ (B : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : finiteAdelicGL2Subgroup ℚ),
      (∀ v, v ∉ B → localAt ℚ v (g : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v, v ∈ B → ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : G2) = n * k) →
      ∃ n : finiteAdelicGL2Subgroup ℚ, n ∈ RSCarrier.finUnipotent ∧
        ∀ w : HeightOneSpectrum (𝓞 ℚ), localAt ℚ w ((n⁻¹ * g : finiteAdelicGL2Subgroup ℚ) : G2) ∈
          AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤ := by
  classical
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro g ha _
    exact ⟨1, Subgroup.one_mem _, fun w => by rw [inv_one, one_mul]; exact ha w (Finset.notMem_empty w)⟩
  | @insert v B hvB ih =>
    intro g ha hc
    obtain ⟨n, ⟨x, rfl⟩, k, hk, hgv⟩ := hc v (Finset.mem_insert_self v B)
    have hn' : (unipotentGL2Hom x : GL (Fin 2) (v.adicCompletion ℚ)) = unipotentGL2 (Multiplicative.toAdd x) := rfl
    rw [hn'] at hgv
    set N : finiteAdelicGL2Subgroup ℚ := ⟨uniAt v (Multiplicative.toAdd x), uniAt_mem_fin v _⟩ with hNdef
    have hNu : N ∈ RSCarrier.finUnipotent := Subgroup.mem_subgroupOf.2 (uniAt_mem_unip v _)
    have ecoe : ((N⁻¹ * g : finiteAdelicGL2Subgroup ℚ) : G2) = (uniAt v (Multiplicative.toAdd x))⁻¹ * (g : G2) := rfl
    have hcv : localAt ℚ v ((N⁻¹ * g : finiteAdelicGL2Subgroup ℚ) : G2) = k := by
      rw [ecoe, map_mul, map_inv, localAt_uniAt_self, hgv, inv_mul_cancel_left]
    have hcne : ∀ {w : HeightOneSpectrum (𝓞 ℚ)}, w ≠ v →
        localAt ℚ w ((N⁻¹ * g : finiteAdelicGL2Subgroup ℚ) : G2) = localAt ℚ w (g : G2) := fun hw => by
      rw [ecoe, map_mul, map_inv, localAt_uniAt_of_ne v _ hw, inv_one, one_mul]
    obtain ⟨n'', hn''u, hn''⟩ := ih (N⁻¹ * g)
      (fun w hwB => by
        by_cases hwv : w = v
        · subst hwv; rw [hcv]; exact hk
        · rw [hcne hwv]; exact ha w (fun h => (Finset.mem_insert.1 h).elim hwv hwB))
      (fun w hwB => by
        have hwv : w ≠ v := fun h => hvB (h ▸ hwB)
        rw [hcne hwv]; exact hc w (Finset.mem_insert_of_mem hwB))
    refine ⟨N * n'', Subgroup.mul_mem _ hNu hn''u, fun w => ?_⟩
    rw [mul_inv_rev, mul_assoc]
    exact hn'' w

end Ws23PosVol

open scoped Pointwise in
open Ws23PosVol in

theorem solution
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] :
    ∃ V : ℝ, 0 < V ∧
      Integrable
        ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun _ => (1 : ℂ)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) ∧
      (∫ g, {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun _ => (1 : ℂ)) g
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) = (V : ℂ) := by
  classical

  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let Kf : Subgroup (finiteAdelicGL2Subgroup ℚ) :=
    (levelOne (𝓞 ℚ) ℚ ⊤ ⊓ finiteAdelicGL2Subgroup ℚ).subgroupOf (finiteAdelicGL2Subgroup ℚ)
  have hH : IsClosed ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) := by
    rw [show ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) =
        Subtype.val ⁻¹' ((adelicUnipotent ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) from rfl]
    exact (isClosed_range_unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).preimage continuous_subtype_val
  haveI : μN.IsMulRightInvariant := ⟨fun g => by
    have h : (fun h : RSCarrier.finUnipotent => h * g) = fun h => g * h := by
      funext h
      apply Subtype.ext
      apply Subtype.ext
      exact mul_comm_of_mem_range_unipotentGL2Hom (Subgroup.mem_subgroupOf.1 h.2) (Subgroup.mem_subgroupOf.1 g.2)
    rw [h]
    exact MeasureTheory.map_mul_left_eq_self μN g⟩
  have hKset : (Kf : Set (finiteAdelicGL2Subgroup ℚ)) =
      Subtype.val ⁻¹' ((levelOne (𝓞 ℚ) ℚ ⊤ ⊓ finiteAdelicGL2Subgroup ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) :
        Set (AdelicGL2 (𝓞 ℚ) ℚ)) := rfl
  have hKset' : (Kf : Set (finiteAdelicGL2Subgroup ℚ)) =
      Subtype.val ⁻¹' ((levelOne (𝓞 ℚ) ℚ ⊤ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) := by
    ext g
    simp only [hKset, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf, g.2, and_true]
  have hKo : IsOpen (Kf : Set (finiteAdelicGL2Subgroup ℚ)) := by
    rw [hKset']
    exact (NumberField.AdelicLevel.isOpen_levelOne (𝓞 ℚ) ℚ top_ne_bot).preimage continuous_subtype_val
  have hKc : IsCompact (Kf : Set (finiteAdelicGL2Subgroup ℚ)) := by
    rw [hKset]
    exact (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ ⊤)

  have hAeq : {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} =
      ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) *
        (Kf : Set (finiteAdelicGL2Subgroup ℚ)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
    constructor
    · intro hg
      obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v, v ∉ T →
          localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
        have h := eventually_mem_localLevelOne (g : AdelicGL2 (𝓞 ℚ) ℚ)
        rw [Filter.eventually_cofinite] at h
        exact ⟨h.toFinset, fun v hv => by_contra fun h' => hv (h.mem_toFinset.2 h')⟩
      obtain ⟨n, hn, hk⟩ := exists_unipotent_forall_localAt_mem T g hT (fun v _ => hg v)
      refine ⟨n, hn, n⁻¹ * g, ?_, mul_inv_cancel_left n g⟩
      show n⁻¹ * g ∈ Kf
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨mem_levelOne_top_of_forall_localAt _ hk, (n⁻¹ * g).2⟩
    · rintro ⟨n, hn, k, hk, rfl⟩ v
      have hk' : ((k : finiteAdelicGL2Subgroup ℚ) : G2) ∈ levelOne (𝓞 ℚ) ℚ ⊤ :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
      refine ⟨localAt ℚ v (n : G2), localAt_mem_range_of_mem_adelicUnipotent v (Subgroup.mem_subgroupOf.1 hn),
        localAt ℚ v (k : G2), localAt_mem_localLevelOne_of_mem_levelOne_top hk' v, ?_⟩
      show localAt ℚ v (((n * k : finiteAdelicGL2Subgroup ℚ)) : G2) = _
      rw [Subgroup.coe_mul, map_mul]
  have hAo : IsOpen {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} := by
    rw [hAeq]; exact hKo.mul_left
  have hAm := hAo.measurableSet

  obtain ⟨hvol, hlt⟩ := HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top μ
    RSCarrier.finUnipotent hH μN Kf hKo hKc
  rw [← hAeq] at hvol hlt
  have hμA : (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))
      {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} =
      ∫⁻ g, {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator
          (fun _ => (1 : ENNReal)) g ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by
    rw [MeasureTheory.lintegral_indicator hAm, MeasureTheory.setLIntegral_const, one_mul]
  have hAtop : (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))
      {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} < ⊤ := by
    rw [hμA]; exact hlt
  have hApos : (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))
      {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} ≠ 0 := by
    rw [hμA, hvol]
    refine (ENNReal.div_pos_iff.mpr ⟨?_, ?_⟩).ne'
    · exact (hKo.measure_pos μ ⟨1, Subgroup.one_mem _⟩).ne'
    · exact ((hH.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top).ne
  refine ⟨((μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))
      {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}).toReal,
    ENNReal.toReal_pos hApos hAtop.ne, ?_, ?_⟩
  · rw [integrable_indicator_iff hAm]
    exact integrableOn_const hAtop.ne
  · rw [MeasureTheory.integral_indicator_const _ hAm, Complex.real_smul, mul_one, measureReal_def]

end S_LanglandsTunnell_RankinSelberg_exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq (solution)
