-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ef5e4b4d-5482-5127-a898-4192b6f655e1

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm

import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul.LanglandsTunnell.RankinSelberg"

open scoped Pointwise

open scoped Pointwise

noncomputable section

namespace LanglandsTunnell
namespace RankinSelberg
namespace BigCellCompact
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open AdelicDock NumberField.AdelicLevel
open scoped Classical

theorem localAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v x hw]

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    glArch (𝓞 ℚ) ℚ (placeEmbed ℚ v x) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := mapMatrix_arch_finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ v x)
  have := congrFun (congrFun h i) j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact this

theorem placeEmbed_mem (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_placeEmbed v x)

section Continuity

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem continuous_splice (a : FiniteAdeleRing R K)
    (ha : ∀ w : HeightOneSpectrum R, a w ∈ w.adicCompletionIntegers K) :
    Continuous (splice R K v a) := by
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal {w | w ≠ v} := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum R => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal {w | w ≠ v}) :=
    fun t => ⟨fun w => splice R K v a t w, by
      rw [Filter.eventually_principal]
      intro w hw
      show splice R K v a t w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K))
      rw [splice_apply_of_ne R K v a t hw]
      exact ha w⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      have : ((fun x => x w) ∘ g) = id := by
        funext t
        exact splice_apply_self R K w a t
      rw [this]
      exact continuous_id
    · have : ((fun x => x w) ∘ g) = fun _ => a w := by
        funext t
        exact splice_apply_of_ne R K v a t hw
      rw [this]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem one_entry_mem (i j : Fin 2) (w : HeightOneSpectrum R) :
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w ∈ w.adicCompletionIntegers K := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem continuous_localMat : Continuous (localMat R K v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_splice R K v _ (one_entry_mem R K i j)).comp
    ((continuous_apply j).comp (continuous_apply i))

theorem continuous_localEmbed : Continuous (localEmbed R K v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_localMat R K v).comp Units.continuous_val
  · exact (continuous_localMat R K v).comp Units.continuous_coe_inv

theorem continuous_finMat : Continuous (finMat R K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_const.prodMk ((continuous_apply j).comp (continuous_apply i))

theorem continuous_finEmbed : Continuous (finEmbed R K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_finMat R K).comp Units.continuous_val
  · exact (continuous_finMat R K).comp Units.continuous_coe_inv

end Continuity

def piList (l : List (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL2 (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  (l.map fun v => placeEmbed ℚ v (localAt ℚ v h)).prod

theorem localAt_piList (l : List (HeightOneSpectrum (𝓞 ℚ))) (hl : l.Nodup) (h : AdelicGL2 (𝓞 ℚ) ℚ)
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ w (piList l h) = if w ∈ l then localAt ℚ w h else 1 := by
  induction l with
  | nil => simp [piList]
  | cons a l ih =>
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    rw [piList, List.map_cons, List.prod_cons, map_mul, show (l.map fun v => placeEmbed ℚ v (localAt ℚ v h)).prod =
      piList l h from rfl, ih hl']
    by_cases hw : w = a
    · subst hw
      rw [localAt_placeEmbed_self, if_neg ha, mul_one]
      simp
    · rw [localAt_placeEmbed_of_ne hw, one_mul]
      by_cases hwl : w ∈ l
      · rw [if_pos hwl, if_pos (List.mem_cons_of_mem a hwl)]
      · rw [if_neg hwl, if_neg (by simp [hw, hwl])]

theorem glArch_piList (l : List (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL2 (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (piList l h) = 1 := by
  rw [piList, map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  exact glArch_placeEmbed v _

theorem continuous_piList (l : List (HeightOneSpectrum (𝓞 ℚ))) : Continuous (piList l) := by
  unfold piList
  refine continuous_list_prod _ (fun v _ => ?_)
  exact ((continuous_finEmbed (𝓞 ℚ) ℚ).comp (continuous_localEmbed (𝓞 ℚ) ℚ v)).comp (continuous_localAt ℚ v)

end LanglandsTunnell.RankinSelberg.BigCellCompact

end

namespace LanglandsTunnell
namespace RankinSelberg
namespace BigCellCompact
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open AdelicDock NumberField.AdelicLevel
open scoped Classical

theorem isLocalLevelOne_top_of_integral (v : HeightOneSpectrum (𝓞 ℚ)) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) : IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [idealBound_top]; exact hm 1 0
  · rw [idealBound_top]; exact (v.adicCompletionIntegers ℚ).sub_mem (hm 1 1) (one_mem _)

theorem mem_localLevelOne_top_of_integral (v : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (v.adicCompletion ℚ))
    (h1 : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (h2 : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ :=
  (mem_localLevelOne_iff (𝓞 ℚ) ℚ v k).mpr ⟨isLocalLevelOne_top_of_integral v _ h1, isLocalLevelOne_top_of_integral v _ h2⟩

theorem localAt_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    (localAt ℚ v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v := rfl

theorem eventually_localAt_mem_localLevelOne (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∀ᶠ v in Filter.cofinite, localAt ℚ v g ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 2,
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v ∈ v.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j
    exact (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2).2
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 2,
      ((((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v ∈ v.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j
    exact ((((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2).2
  filter_upwards [h1, h2] with v hv1 hv2
  refine mem_localLevelOne_top_of_integral v _ (fun i j => ?_) (fun i j => ?_)
  · rw [localAt_apply]; exact hv1 i j
  · rw [← map_inv, localAt_apply]; exact hv2 i j

theorem mem_levelOne_of_forall_localAt {N : Ideal (𝓞 ℚ)} (z : AdelicGL2 (𝓞 ℚ) ℚ)
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), localAt ℚ w z ∈ localLevelOne (𝓞 ℚ) ℚ w N) :
    z ∈ levelOne (𝓞 ℚ) ℚ N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  have hz : ∀ w, IsLocalLevelOne (𝓞 ℚ) ℚ w N (localAt ℚ w z : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) ∧
      IsLocalLevelOne (𝓞 ℚ) ℚ w N (((localAt ℚ w z)⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) :=
    fun w => (mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).mp (h w)
  constructor
  · refine ⟨⟨fun i j w => (hz w).1.integral i j, fun w => (hz w).1.lowerLeft⟩, fun w => ?_⟩
    have := (hz w).1.lowerRight
    rwa [coe_sub_apply, coe_one_apply]
  · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
    · have := (hz w).2.integral i j; rwa [← map_inv] at this
    · have := (hz w).2.lowerLeft; rwa [← map_inv] at this
    · have := (hz w).2.lowerRight
      rw [← map_inv] at this
      rw [← map_inv, coe_sub_apply, coe_one_apply]
      exact this

theorem localAt_unipotentGL2 (v : HeightOneSpectrum (𝓞 ℚ)) (X : AdeleRing (𝓞 ℚ) ℚ) :
    localAt ℚ v (unipotentGL2 X) = unipotentGL2 (X.2 v) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [localAt_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem glArch_unipotentGL2 (X : AdeleRing (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (unipotentGL2 X) = unipotentGL2 X.1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

end LanglandsTunnell.RankinSelberg.BigCellCompact

open LanglandsTunnell.RankinSelberg.BigCellCompact in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hsupp : ∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, ‖W g * F g‖ ≤ B₀) ∧
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
            ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
        W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
            ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
              localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) :
    ∃ K' : Set (finiteAdelicGL2Subgroup ℚ), IsCompact K' ∧
      {g : finiteAdelicGL2Subgroup ℚ |
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k) ∧ W g * F g ≠ 0} ⊆
        ((RSCarrier.finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) * K' := by
  classical
  obtain ⟨Cpt, B₀, hCpt, -, hmain⟩ := hsupp

  set K₁ : Set (finiteAdelicGL2Subgroup ℚ) := ((↑) : finiteAdelicGL2Subgroup ℚ → AdelicGL2 (𝓞 ℚ) ℚ) ⁻¹'
    ((NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ ⊤ ⊓ finiteAdelicGL2Subgroup ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) with hK₁
  have hK₁c : IsCompact K₁ :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ ⊤)

  set l : List (HeightOneSpectrum (𝓞 ℚ)) := S.toList with hl
  have hln : l.Nodup := by rw [hl]; exact S.nodup_toList
  have hlmem : ∀ w, w ∈ l ↔ w ∈ S := fun w => by rw [hl, Finset.mem_toList]
  let πS : finiteAdelicGL2Subgroup ℚ → finiteAdelicGL2Subgroup ℚ := fun h =>
    ⟨piList l (h : AdelicGL2 (𝓞 ℚ) ℚ), (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_piList l _)⟩
  have hπc : Continuous πS :=
    ((continuous_piList l).comp continuous_subtype_val).subtype_mk _
  refine ⟨(πS '' Cpt) * K₁, (hCpt.image hπc).mul hK₁c, ?_⟩
  rintro g ⟨hcell, hz⟩
  obtain ⟨n, h, hh, hS⟩ := hmain g hcell hz

  obtain ⟨yn, hyn⟩ := Subgroup.mem_subgroupOf.mp n.2
  have hnval : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 yn.toAdd := by rw [← hyn]; rfl
  set a : finiteAdelicGL2Subgroup ℚ := (n : finiteAdelicGL2Subgroup ℚ) * g with ha
  have haval : (a : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 yn.toAdd * (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    rw [ha, Subgroup.coe_mul, hnval]

  have hchoice : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ t : v.adicCompletion ℚ,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (a : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 t * k := by
    intro v hv
    obtain ⟨n', hn', k, hk, hgk⟩ := hcell v hv
    obtain ⟨y', rfl⟩ := hn'
    refine ⟨(yn.toAdd).2 v + y'.toAdd, k, hk, ?_⟩
    rw [haval, map_mul, hgk, localAt_unipotentGL2, unipotentGL2_add, mul_assoc]
    rfl

  let x : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ := fun v =>
    if hv : v ∉ S ∧ localAt ℚ v (a : AdelicGL2 (𝓞 ℚ) ℚ) ∉ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ then
      Classical.choose (hchoice v hv.1) else 0
  have hx0 : ∀ v, localAt ℚ v (a : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → x v = 0 := by
    intro v hv; simp only [x]; rw [dif_neg (fun h => h.2 hv)]
  have hxS : ∀ v ∈ S, x v = 0 := by
    intro v hv; simp only [x]; rw [dif_neg (fun h => h.1 hv)]
  have hxint : ∀ᶠ v in Filter.cofinite, x v ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    filter_upwards [eventually_localAt_mem_localLevelOne (a : AdelicGL2 (𝓞 ℚ) ℚ)] with v hv
    rw [hx0 v hv]; exact zero_mem _
  let xf : FiniteAdeleRing (𝓞 ℚ) ℚ := ⟨x, hxint⟩
  let X : AdeleRing (𝓞 ℚ) ℚ := ((0 : InfiniteAdeleRing ℚ), xf)
  have hX2 : ∀ v, (X.2) v = x v := fun v => rfl

  have hmfin : (unipotentGL2 (-X) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteAdelicGL2Subgroup ℚ := by
    rw [mem_finiteAdelicGL2Subgroup_iff, glArch_unipotentGL2]
    have : (-X).1 = 0 := by show -(0 : InfiniteAdeleRing ℚ) = 0; exact neg_zero
    rw [this, unipotentGL2_zero]
  let m : finiteAdelicGL2Subgroup ℚ := ⟨unipotentGL2 (-X), hmfin⟩
  have hmN : m ∈ RSCarrier.finUnipotent := Subgroup.mem_subgroupOf.mpr ⟨Multiplicative.ofAdd (-X), rfl⟩
  have hmloc : ∀ v, localAt ℚ v (m : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (-(x v)) := by
    intro v
    show localAt ℚ v (unipotentGL2 (-X)) = _
    rw [localAt_unipotentGL2]; rfl

  have hk'S : ∀ v ∈ S, localAt ℚ v ((m * a : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
      localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro v hv
    rw [Subgroup.coe_mul, map_mul, hmloc, hxS v hv, neg_zero, unipotentGL2_zero, one_mul, ha]
    exact hS v hv
  have hk'off : ∀ v, v ∉ S → localAt ℚ v ((m * a : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
    intro v hv
    rw [Subgroup.coe_mul, map_mul, hmloc]
    by_cases hin : localAt ℚ v (a : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤
    · rw [hx0 v hin, neg_zero, unipotentGL2_zero, one_mul]; exact hin
    · have hxv : x v = Classical.choose (hchoice v hv) := by simp only [x]; rw [dif_pos ⟨hv, hin⟩]
      obtain ⟨k, hk, hak⟩ := Classical.choose_spec (hchoice v hv)
      rw [hak, hxv, ← mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, one_mul]
      exact hk

  set y : finiteAdelicGL2Subgroup ℚ := (πS h)⁻¹ * (m * a) with hy
  have hyK : y ∈ K₁ := by
    rw [hK₁]
    refine ⟨mem_levelOne_of_forall_localAt _ (fun w => ?_), y.2⟩
    rw [hy, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    show (localAt ℚ w (piList l (h : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ * _ ∈ _
    rw [localAt_piList l hln]
    by_cases hw : w ∈ S
    · rw [if_pos ((hlmem w).mpr hw), hk'S w hw, inv_mul_cancel]; exact one_mem _
    · rw [if_neg (fun h' => hw ((hlmem w).mp h')), inv_one, one_mul]; exact hk'off w hw

  refine Set.mem_mul.mpr ⟨(n : finiteAdelicGL2Subgroup ℚ)⁻¹ * m⁻¹,
    RSCarrier.finUnipotent.mul_mem (RSCarrier.finUnipotent.inv_mem n.2) (RSCarrier.finUnipotent.inv_mem hmN),
    πS h * y, Set.mem_mul.mpr ⟨πS h, ⟨h, hh, rfl⟩, y, hyK, rfl⟩, ?_⟩
  rw [hy, ha]
  group

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_bigCell_inter_support_subset_finUnipotent_mul (solution)
