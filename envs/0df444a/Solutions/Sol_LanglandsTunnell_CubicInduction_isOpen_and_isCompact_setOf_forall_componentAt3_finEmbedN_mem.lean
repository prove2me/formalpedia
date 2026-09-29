-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d0246882-5dfa-51e5-80f4-89f4faa265e7

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem

set_option autoImplicit false

open IsDedekindDomain
open scoped NumberField

namespace LevelSetCompactOpen

open LanglandsTunnell.CubicInduction
open Matrix IsDedekindDomain NumberField AutomorphicForm

noncomputable section

section Components

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_componentAt3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_localToAdelic3 (h : LocalGL3 v) :
    ((localToAdelic3 v h : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ
        (localMatN (Fin 3) (𝓞 ℚ) ℚ v (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) :=
  rfl

private theorem componentAt3_localToAdelic3_self (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ v (localToAdelic3 v h) = h := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_self]

private theorem componentAt3_localToAdelic3_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (h : LocalGL3 v) :
    componentAt3 (𝓞 ℚ) ℚ w (localToAdelic3 v h) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_finMatN, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ v _ hw, Units.val_one]

private theorem archComponent3_localToAdelic3 (h : LocalGL3 v) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 v h) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

end Components

section OpenMaximal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_setOf_forall_entry_mem {B : Set (v.adicCompletion ℚ)} (hB : IsOpen B) :
    IsOpen {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) | ∀ i j, M i j ∈ B} := by
  simp_rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (continuous_id.matrix_elem i j).isOpen_preimage B hB

private theorem isOpen_localMaximalCompact3 :
    IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hI : IsOpen {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
      ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}} :=
    isOpen_setOf_forall_entry_mem v
      (by simpa using AdelicLevel.isOpen_setOf_valued_le v (1 : v.adicCompletion ℚ) one_ne_zero)
  have hset : ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (Units.val ⁻¹' {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
          ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}}) ∩
        ((fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ⁻¹'
          {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) |
            ∀ i j, M i j ∈ {z : v.adicCompletion ℚ | Valued.v z ≤ 1}}) :=
    rfl
  rw [hset]
  exact (Units.continuous_val.isOpen_preimage _ hI).inter (Units.continuous_coe_inv.isOpen_preimage _ hI)

end OpenMaximal

section LevelCompact

private scoped instance t2Space_matrixFin3_finiteAdeleRing : T2Space (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → (FiniteAdeleRing (𝓞 ℚ) ℚ)))

private def finComponent3 (p : HeightOneSpectrum (𝓞 ℚ)) : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) →* LocalGL3 p :=
  (componentAt3 (𝓞 ℚ) ℚ p).comp (finEmbedN (Fin 3) (𝓞 ℚ) ℚ)

private theorem finComponent3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    finComponent3 p k = componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) := rfl

private theorem finComponent3_localEmbedN_self (p : HeightOneSpectrum (𝓞 ℚ)) (τ : LocalGL3 p) :
    finComponent3 p (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ) = τ :=
  componentAt3_localToAdelic3_self p τ

private theorem finComponent3_localEmbedN_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (τ : LocalGL3 p) :
    finComponent3 q (localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ) = 1 :=
  componentAt3_localToAdelic3_of_ne p hq τ

private theorem coe_finComponent3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (i j : Fin 3) :
    ((finComponent3 p k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      ((k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) p :=
  rfl

private def integralMatrices : Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  {m | ∀ i j, m i j ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ}

private theorem isCompact_integralMatrices : IsCompact integralMatrices := by
  have hset : integralMatrices =
      (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :
        Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    exact Set.ext fun m =>
      ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => AdelicBox.isCompact_integralFiniteAdeles ℚ

private theorem isClosed_range_embedProduct_matrix :
    IsClosed (Set.range (Units.embedProduct (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)))) := by
  have h : Set.range (Units.embedProduct (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      {q : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) × (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ |
        q.1 * MulOpposite.unop q.2 = 1 ∧ MulOpposite.unop q.2 * q.1 = 1} := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨q.1, MulOpposite.unop q.2, h1, h2⟩, Prod.ext rfl (MulOpposite.op_unop q.2)⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

private def integralPoints : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  Units.embedProduct (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ⁻¹'
    (integralMatrices ×ˢ (MulOpposite.op '' integralMatrices))

private theorem isCompact_integralPoints : IsCompact integralPoints :=
  (Units.isInducing_embedProduct (M := Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))).isCompact_preimage
    isClosed_range_embedProduct_matrix
    (isCompact_integralMatrices.prod (isCompact_integralMatrices.image MulOpposite.continuous_op))

private theorem mem_integralPoints_of_forall_mem_localMaximalCompact3 {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    k ∈ integralPoints := by
  show (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ integralMatrices ∧
    MulOpposite.op ((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
        Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈
      MulOpposite.op '' integralMatrices
  refine ⟨fun i j p => ?_, Set.mem_image_of_mem _ fun i j p => ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← coe_finComponent3_apply]
    exact (hk p).1 i j
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← coe_finComponent3_apply, map_inv]
    exact (hk p).2 i j

open scoped Classical in

private theorem exists_isCompact_superset_of_finset (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p),
      (∀ p ∈ S, IsCompact (K' p : Set (LocalGL3 p))) → (∀ p ∉ S, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) →
      ∃ C : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact C ∧
        {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) | ∀ p, finComponent3 p k ∈ K' p} ⊆ C := by
  refine Finset.induction_on S ?_ ?_
  · intro K' _ hmax
    refine ⟨integralPoints, isCompact_integralPoints, fun k hk => ?_⟩
    exact mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
      rw [← hmax p (by simp)]
      exact hk p
  · intro p S hpS ih K' hcpt hmax
    obtain ⟨C', hC', hsub'⟩ := ih (Function.update K' p (localMaximalCompact3 (𝓞 ℚ) ℚ p))
      (fun q hq => by
        have hqp : q ≠ p := fun h => hpS (h ▸ hq)
        rw [Function.update_of_ne hqp]
        exact hcpt q (Finset.mem_insert_of_mem hq))
      (fun q hq => by
        by_cases hqp : q = p
        · subst hqp
          exact Function.update_self ..
        · rw [Function.update_of_ne hqp]
          exact hmax q fun h => hq ((Finset.mem_insert.mp h).elim (fun h' => absurd h' hqp) id))
    have hKp : IsCompact (K' p : Set (LocalGL3 p)) := hcpt p (Finset.mem_insert_self p S)
    obtain ⟨T, hT⟩ := hKp.elim_finite_subcover
      (fun τ : LocalGL3 p => {x : LocalGL3 p | τ⁻¹ * x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p})
      (fun τ => (continuous_const.mul continuous_id).isOpen_preimage _ (isOpen_localMaximalCompact3 p))
      (fun x _ => Set.mem_iUnion.mpr ⟨x, by simp only [Set.mem_setOf_eq, inv_mul_cancel]; exact one_mem _⟩)
    refine ⟨⋃ τ ∈ T, (fun k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) => localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ * k) '' C',
      T.finite_toSet.isCompact_biUnion fun τ _ => hC'.image (continuous_const.mul continuous_id), fun k hk => ?_⟩
    obtain ⟨τ, hτT, hτ⟩ := Set.mem_iUnion₂.mp (hT (hk p))
    refine Set.mem_biUnion hτT ⟨(localEmbedN (Fin 3) (𝓞 ℚ) ℚ p τ)⁻¹ * k, hsub' fun q => ?_, mul_inv_cancel_left _ _⟩
    rw [map_mul, map_inv]
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self, finComponent3_localEmbedN_self]
      exact hτ
    · rw [Function.update_of_ne hqp, finComponent3_localEmbedN_of_ne hqp, inv_one, one_mul]
      exact hk q

private theorem exists_isCompact_forall_componentAt3_finEmbedN_mem_subset
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ C : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact C ∧
      {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ⊆ C := by
  have hfin := Filter.eventually_cofinite.mp hcof
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_superset_of_finset hfin.toFinset K' (fun p _ => hcpt p)
    (fun p hp => by simpa using hp)
  exact ⟨C, hC, fun k hk => hsub fun p => hk p⟩

private theorem continuous_finComponent3 (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous (finComponent3 p) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_matrix fun i j =>
      (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (Units.continuous_val.matrix_elem i j)
  · simp only [← map_inv]
    exact continuous_matrix fun i j =>
      (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (Units.continuous_coe_inv.matrix_elem i j)

private def levelSubgroup (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    Subgroup (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) where
  carrier := {k | ∀ p, finComponent3 p k ∈ K' p}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro p
    rw [map_one]
    exact one_mem _
  mul_mem' := by
    intro a b ha hb p
    rw [map_mul]
    exact mul_mem (ha p) (hb p)
  inv_mem' := by
    intro a ha p
    rw [map_inv]
    exact inv_mem (ha p)

private theorem mem_levelSubgroup_iff (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
    k ∈ levelSubgroup K' ↔ ∀ p, finComponent3 p k ∈ K' p := Iff.rfl

private theorem coe_levelSubgroup (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    (levelSubgroup K' : Set (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := rfl

private theorem isOpen_integralMatrices : IsOpen integralMatrices := by
  have hset : integralMatrices =
      (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :
        Set (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    exact Set.ext fun m =>
      ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j)⟩
  rw [hset]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => AdelicBox.isOpen_integralFiniteAdeles ℚ

private theorem isOpen_integralPoints : IsOpen integralPoints :=
  Units.continuous_embedProduct.isOpen_preimage _
    (isOpen_integralMatrices.prod (MulOpposite.opHomeomorph.isOpenMap _ isOpen_integralMatrices))

private theorem finComponent3_mem_localMaximalCompact3_of_mem_integralPoints
    {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))}
    (hk : k ∈ integralPoints)
    (p : HeightOneSpectrum (𝓞 ℚ)) : finComponent3 p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨m, hm, hmk⟩ := h2
  have hmk' : MulOpposite.op m =
      MulOpposite.op ((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) :
        Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    hmk
  have hm' : m = ((k⁻¹ : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    MulOpposite.op_injective hmk'
  subst hm'
  change _ ∧ _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1 i j p
  · rw [← map_inv, coe_finComponent3_apply, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hm i j p

private theorem one_mem_integralPoints : (1 : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) ∈ integralPoints :=
  mem_integralPoints_of_forall_mem_localMaximalCompact3 fun p => by
    rw [map_one]
    exact one_mem _

open scoped Classical in

private theorem isOpen_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
  rw [← coe_levelSubgroup]
  refine Subgroup.isOpen_of_mem_nhds (levelSubgroup K') (g := 1) ?_
  have hfin := Filter.eventually_cofinite.mp hcof
  have hW : IsOpen (integralPoints ∩ ⋂ p ∈ hfin.toFinset, finComponent3 p ⁻¹' (K' p : Set (LocalGL3 p))) :=
    isOpen_integralPoints.inter
      (isOpen_biInter_finset fun p _ => (continuous_finComponent3 p).isOpen_preimage _ (hopen p))
  refine Filter.mem_of_superset (hW.mem_nhds ⟨one_mem_integralPoints, ?_⟩) ?_
  · exact Set.mem_iInter₂.mpr fun p _ => by
      show finComponent3 p 1 ∈ K' p
      rw [map_one]
      exact one_mem _
  · intro k hk
    obtain ⟨hint, hS⟩ := hk
    rw [SetLike.mem_coe, mem_levelSubgroup_iff]
    intro p
    by_cases hp : p ∈ hfin.toFinset
    · exact Set.mem_iInter₂.mp hS p hp
    · have hmax : K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p := by simpa using hp
      rw [hmax]
      exact finComponent3_mem_localMaximalCompact3_of_mem_integralPoints hint p

private theorem isCompact_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsCompact {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_forall_componentAt3_finEmbedN_mem_subset K' hcpt hcof
  have hclosed : IsClosed {k : (GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) |
      ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by
    rw [← coe_levelSubgroup]
    exact Subgroup.isClosed_of_isOpen _ (isOpen_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcof)
  exact hC.of_isClosed_subset hclosed hsub

end LevelCompact

end

end LevelSetCompactOpen
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem.LevelSetCompactOpen"

open LanglandsTunnell.CubicInduction in

theorem solution
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {k : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ∧
      IsCompact {k : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} :=
  ⟨LevelSetCompactOpen.isOpen_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcof,
    LevelSetCompactOpen.isCompact_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcpt hcof⟩

end S_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem (solution)
