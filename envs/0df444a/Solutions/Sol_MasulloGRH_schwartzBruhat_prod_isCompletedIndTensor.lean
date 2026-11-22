-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_prod_isCompletedIndTensor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:26:14.525272+00:00
-- url     : https://prove2.me/submissions/78856070-9726-4fbc-adde-812f6146d58c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_TopologicalTensorProduct_Completion
import Theorems.Thm_MasulloGRH_indTensor_eq_projTensor_of_isFrechet
import Theorems.Thm_MasulloGRH_continuous_indTensor_iff
import Theorems.Thm_MasulloGRH_indTensor_isHLCS
import Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure
import Theorems.Thm_MasulloGRH_schwartzBruhat_prod_stages_isCompletedProjTensor

open TensorProduct Topology

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Sol_MasulloGRH_schwartzBruhat_prod_isCompletedIndTensor

open MasulloGRH

/-- The topology defined by a single seminorm. -/
noncomputable abbrev semTop {B : Type u} [AddCommGroup B] [Module ℂ B] (Q : Seminorm ℂ B) :
    TopologicalSpace B :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) (fun _ : PUnit.{u+1} => Q)).topology

lemma semTop_withSeminorms {B : Type u} [AddCommGroup B] [Module ℂ B] (Q : Seminorm ℂ B) :
    @WithSeminorms ℂ B PUnit.{u+1} _ _ _ (fun _ => Q) (semTop Q) :=
  @WithSeminorms.mk ℂ B PUnit.{u+1} _ _ _ (fun _ => Q) (semTop Q) rfl

lemma continuous_semTop {A B : Type u} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddCommGroup B] [Module ℂ B] (Q : Seminorm ℂ B) (f : A →ₗ[ℂ] B)
    (hf : Continuous (fun a => Q (f a))) : @Continuous A B _ (semTop Q) f := by
  letI : TopologicalSpace B := semTop Q
  exact WithSeminorms.continuous_of_continuous_comp (semTop_withSeminorms Q) f (fun _ => hf)

lemma seminorm_continuous_semTop {B : Type u} [AddCommGroup B] [Module ℂ B] (Q : Seminorm ℂ B) :
    @Continuous B ℝ (semTop Q) _ Q := by
  letI : TopologicalSpace B := semTop Q
  exact (semTop_withSeminorms Q).continuous_seminorm PUnit.unit

/-- Universal property of a locally convex inductive limit topology given by submodules. -/
lemma continuous_of_final {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (X : ℕ → Submodule ℂ E)
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (hW : IsLocallyConvexTopology W ‹_›) (L : E →ₗ[ℂ] W)
    (hL : ∀ n, Continuous (fun x : X n => L x)) : Continuous L := by
  obtain ⟨ι, hι, p, hp⟩ := hW
  rw [continuous_iff_le_induced, htop]
  exact sInf_le ⟨⟨ι, hι, p.comp L, LinearMap.withSeminorms_induced hp L⟩,
    fun n => continuous_induced_rng.2 (hL n)⟩

/-- A seminorm that is continuous on every step of a locally convex inductive limit is
continuous. -/
lemma seminorm_continuous_of_final {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (X : ℕ → Submodule ℂ E)
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (Q : Seminorm ℂ E) (hQ : ∀ n, Continuous (fun x : X n => Q x)) : Continuous Q := by
  have hle : ‹TopologicalSpace E› ≤ semTop Q := by
    rw [htop]
    exact sInf_le ⟨⟨PUnit, inferInstance, fun _ => Q, semTop_withSeminorms Q⟩,
      fun n => continuous_semTop Q (X n).subtype (hQ n)⟩
  exact continuous_le_dom hle (seminorm_continuous_semTop Q)

/-- Comparison of a group topology with a topology given by seminorms. -/
lemma le_of_forall_seminorm_continuous {V : Type u} [AddCommGroup V] [Module ℂ V]
    (t₁ t₂ : TopologicalSpace V) (h₁ : @IsTopologicalAddGroup V t₁ _) {ι : Type u}
    (p : SeminormFamily ℂ V ι) (hp : @WithSeminorms ℂ V ι _ _ _ p t₂)
    (hc : ∀ i, @Continuous V ℝ t₁ _ (p i)) : t₁ ≤ t₂ := by
  rw [← @continuous_id_iff_le V t₁ t₂]
  exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ V V ι _ _ _ _ _ _ (RingHom.id ℂ) _ p
    t₁ h₁ t₂ hp LinearMap.id (fun i => hc i)

/-- Extension of a seminorm along a linear map inducing the topology (infimal convolution). -/
lemma exists_extend_seminorm {A B : Type u} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [TopologicalSpace B] (hB : IsLocallyConvexTopology B ‹_›) (L : A →ₗ[ℂ] B)
    (q : Seminorm ℂ A) (hq : @Continuous A ℝ (TopologicalSpace.induced L ‹_›) _ q) :
    ∃ Q : Seminorm ℂ B, Continuous Q ∧ ∀ a, Q (L a) = q a := by
  obtain ⟨ι, hι, P, hP⟩ := hB
  have hTAG : IsTopologicalAddGroup B := hP.topologicalAddGroup
  letI : TopologicalSpace A := TopologicalSpace.induced L ‹_›
  have hind : IsInducing L := ⟨rfl⟩
  haveI : PolynormableSpace ℂ B := hP.toPolynormableSpace
  obtain ⟨p, hpc, hqp⟩ := Seminorm.exists_le_comp_of_isInducing hq hind
  let f : B → ℝ := fun b => ⨅ a : A, q a + p (b - L a)
  have hbdd : ∀ b, BddBelow (Set.range fun a : A => q a + p (b - L a)) := fun b =>
    ⟨0, by rintro _ ⟨a, rfl⟩; positivity⟩
  have hfle : ∀ b, f b ≤ p b := fun b => by
    refine (ciInf_le (hbdd b) 0).trans ?_
    simp
  have hf0 : ∀ b, 0 ≤ f b := fun b => le_ciInf fun a => by positivity
  have hfL : ∀ a, f (L a) = q a := by
    intro a
    apply le_antisymm
    · refine (ciInf_le (hbdd _) a).trans ?_
      simp
    · refine le_ciInf fun a' => ?_
      have h1 : q a ≤ q a' + q (a - a') := by
        simpa using map_add_le_add q a' (a - a')
      have h2 : q (a - a') ≤ p (L a - L a') := by
        rw [← map_sub]
        exact hqp (a - a')
      linarith
  have hadd : ∀ x y, f (x + y) ≤ f x + f y := by
    intro x y
    have key : ∀ a a', f (x + y) ≤ (q a + p (x - L a)) + (q a' + p (y - L a')) := by
      intro a a'
      refine (ciInf_le (hbdd _) (a + a')).trans ?_
      have h1 : q (a + a') ≤ q a + q a' := map_add_le_add q a a'
      have h2 : p (x + y - L (a + a')) ≤ p (x - L a) + p (y - L a') := by
        have : x + y - L (a + a') = (x - L a) + (y - L a') := by rw [map_add]; abel
        rw [this]
        exact map_add_le_add p _ _
      linarith
    have h1 : ∀ a, f (x + y) - (q a + p (x - L a)) ≤ f y := fun a =>
      le_ciInf fun a' => by linarith [key a a']
    have h2 : f (x + y) - f y ≤ f x := le_ciInf fun a => by linarith [h1 a]
    linarith
  have hsmul : ∀ (r : ℂ) (x : B), f (r • x) ≤ ‖r‖ * f x := by
    intro r x
    rcases eq_or_ne r 0 with rfl | hr
    · simp only [zero_smul, norm_zero, zero_mul]
      exact (hfle 0).trans (by simp)
    · rw [Real.mul_iInf_of_nonneg (norm_nonneg r)]
      refine le_ciInf fun a => ?_
      refine (ciInf_le (hbdd _) (r • a)).trans (le_of_eq ?_)
      rw [L.map_smul, ← smul_sub, map_smul_eq_mul q, map_smul_eq_mul p, mul_add]
  have hf00 : f 0 = 0 := le_antisymm ((hfle 0).trans (by simp)) (hf0 0)
  refine ⟨Seminorm.ofSMulLE f hf00 hadd hsmul, ?_, fun a => hfL a⟩
  exact Seminorm.continuous_of_le hpc (fun b => hfle b)

section stages

variable {E F Y : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- The canonical map `X₁ n ⊗ X₂ n → E ⊗ F`. -/
noncomputable abbrev μ (X₁ : ℕ → Submodule ℂ E) (X₂ : ℕ → Submodule ℂ F) (n : ℕ) :
    X₁ n ⊗[ℂ] X₂ n →ₗ[ℂ] E ⊗[ℂ] F :=
  TensorProduct.map (X₁ n).subtype (X₂ n).subtype

/-- The transition map `X₁ n ⊗ X₂ n → X₁ m ⊗ X₂ m`. -/
noncomputable abbrev ιmap (X₁ : ℕ → Submodule ℂ E) (X₂ : ℕ → Submodule ℂ F)
    (hm₁ : Monotone X₁) (hm₂ : Monotone X₂) {n m : ℕ} (h : n ≤ m) :
    X₁ n ⊗[ℂ] X₂ n →ₗ[ℂ] X₁ m ⊗[ℂ] X₂ m :=
  TensorProduct.map (Submodule.inclusion (hm₁ h)) (Submodule.inclusion (hm₂ h))

lemma μ_ιmap (X₁ : ℕ → Submodule ℂ E) (X₂ : ℕ → Submodule ℂ F)
    (hm₁ : Monotone X₁) (hm₂ : Monotone X₂) {n m : ℕ} (h : n ≤ m) (v : X₁ n ⊗[ℂ] X₂ n) :
    μ X₁ X₂ m (ιmap X₁ X₂ hm₁ hm₂ h v) = μ X₁ X₂ n v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [μ, ιmap]
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add]

lemma exists_μ (X₁ : ℕ → Submodule ℂ E) (X₂ : ℕ → Submodule ℂ F)
    (hm₁ : Monotone X₁) (hm₂ : Monotone X₂)
    (hex₁ : ∀ x, ∃ n, x ∈ X₁ n) (hex₂ : ∀ y, ∃ n, y ∈ X₂ n) (u : E ⊗[ℂ] F) :
    ∃ n v, μ X₁ X₂ n v = u := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := hex₁ x
    obtain ⟨b, hb⟩ := hex₂ y
    refine ⟨max a b, ⟨x, hm₁ (le_max_left a b) ha⟩ ⊗ₜ[ℂ] ⟨y, hm₂ (le_max_right a b) hb⟩, ?_⟩
    simp [μ]
  | add u w hu hw =>
    obtain ⟨a, v, rfl⟩ := hu
    obtain ⟨b, v', rfl⟩ := hw
    refine ⟨max a b, ιmap X₁ X₂ hm₁ hm₂ (le_max_left a b) v +
      ιmap X₁ X₂ hm₁ hm₂ (le_max_right a b) v', ?_⟩
    rw [map_add, μ_ιmap, μ_ιmap]

lemma continuous_tmul_ind_left (x : E) :
    @Continuous F (E ⊗[ℂ] F) _ (indTensorTopology E F) (fun y => x ⊗ₜ[ℂ] y) :=
  continuous_sInf_rng.2 fun _ ht => ht.2.1 x

lemma continuous_tmul_ind_right (y : F) :
    @Continuous E (E ⊗[ℂ] F) _ (indTensorTopology E F) (fun x => x ⊗ₜ[ℂ] y) :=
  continuous_sInf_rng.2 fun _ ht => ht.2.2 y

lemma continuous_tmul_proj_left (x : E) :
    @Continuous F (E ⊗[ℂ] F) _ (projTensorTopology E F) (fun y => x ⊗ₜ[ℂ] y) :=
  continuous_sInf_rng.2 fun _ ht => ht.2.comp (continuous_const.prodMk continuous_id)

lemma continuous_tmul_proj_right (y : F) :
    @Continuous E (E ⊗[ℂ] F) _ (projTensorTopology E F) (fun x => x ⊗ₜ[ℂ] y) :=
  continuous_sInf_rng.2 fun _ ht => ht.2.comp (continuous_id.prodMk continuous_const)

/-- The core of the gluing argument: every continuous seminorm of `E ⊗_ι F` is the restriction
along `j` of a continuous seminorm of `Y`. -/
lemma exists_seminorm_extension
    (hE : IsHLCS E) (hF : IsHLCS F) (hY : IsHLCS Y)
    (X₁ : ℕ → Submodule ℂ E) (X₂ : ℕ → Submodule ℂ F) (Z : ℕ → Submodule ℂ Y)
    (hm₁ : Monotone X₁) (hm₂ : Monotone X₂) (hmZ : Monotone Z)
    (hex₁ : ∀ x, ∃ n, x ∈ X₁ n) (hex₂ : ∀ y, ∃ n, y ∈ X₂ n) (hexZ : ∀ z, ∃ n, z ∈ Z n)
    (hfr₁ : ∀ n, IsFrechet (X₁ n)) (hfr₂ : ∀ n, IsFrechet (X₂ n))
    (htopZ : ‹TopologicalSpace Y› =
      sInf {t | IsLocallyConvexTopology Y t ∧ ∀ n, @Continuous (Z n) Y _ t Subtype.val})
    (j : E ⊗[ℂ] F →ₗ[ℂ] Y) (jn : ∀ n, X₁ n ⊗[ℂ] X₂ n →ₗ[ℂ] Z n)
    (hjμ : ∀ n v, j (μ X₁ X₂ n v) = (jn n v : Y))
    (hcomp : ∀ n, IsCompletedProjTensor (X₁ n) (X₂ n) (jn n))
    (q : Seminorm ℂ (E ⊗[ℂ] F)) (hq : @Continuous _ ℝ (indTensorTopology E F) _ q) :
    ∃ Q : Seminorm ℂ Y, Continuous Q ∧ ∀ u, Q (j u) = q u := by
  classical
  have : T2Space E := hE.2
  have : T2Space F := hF.2
  have hTAGY : IsTopologicalAddGroup Y := by
    obtain ⟨ι, _, p, hp⟩ := hY.1
    exact hp.topologicalAddGroup
  have hX₁ : ∀ n, IsHLCS (X₁ n) := fun n => ⟨(hfr₁ n).1, inferInstance⟩
  have hX₂ : ∀ n, IsHLCS (X₂ n) := fun n => ⟨(hfr₂ n).1, inferInstance⟩
  have hTlc := (indTensor_isHLCS E F hE hF).1
  -- the stage maps are continuous from the projective topology
  have hμc : ∀ n, @Continuous _ _ (projTensorTopology (X₁ n) (X₂ n)) (indTensorTopology E F)
      (μ X₁ X₂ n) := by
    intro n
    rw [← indTensor_eq_projTensor_of_isFrechet (X₁ n) (X₂ n) (hfr₁ n) (hfr₂ n)]
    letI : TopologicalSpace (E ⊗[ℂ] F) := indTensorTopology E F
    refine (continuous_indTensor_iff (X₁ n) (X₂ n) (hX₁ n) (hX₂ n) (E ⊗[ℂ] F) hTlc
      (μ X₁ X₂ n)).2 ⟨fun x => ?_, fun y => ?_⟩
    · have : (fun y : X₂ n => μ X₁ X₂ n (x ⊗ₜ[ℂ] y)) =
          (fun y : F => (x : E) ⊗ₜ[ℂ] y) ∘ Subtype.val := by
        funext y; simp [μ]
      rw [this]
      exact (continuous_tmul_ind_left (x : E)).comp continuous_subtype_val
    · have : (fun x : X₁ n => μ X₁ X₂ n (x ⊗ₜ[ℂ] y)) =
          (fun x : E => x ⊗ₜ[ℂ] (y : F)) ∘ Subtype.val := by
        funext x; simp [μ]
      rw [this]
      exact (continuous_tmul_ind_right (y : F)).comp continuous_subtype_val
  have hqn : ∀ n, @Continuous _ ℝ (TopologicalSpace.induced (jn n) inferInstance) _
      (q.comp (μ X₁ X₂ n)) := by
    intro n
    rw [← (hcomp n).2.2.2.1]
    letI : TopologicalSpace (X₁ n ⊗[ℂ] X₂ n) := projTensorTopology (X₁ n) (X₂ n)
    letI : TopologicalSpace (E ⊗[ℂ] F) := indTensorTopology E F
    exact hq.comp (hμc n)
  choose Qn hQnc hQnj using fun n =>
    exists_extend_seminorm (hcomp n).1.1 (jn n) (q.comp (μ X₁ X₂ n)) (hqn n)
  -- compatibility of the extensions
  have hjι : ∀ n m (h : n ≤ m) v,
      jn m (ιmap X₁ X₂ hm₁ hm₂ h v) = ⟨(jn n v : Y), hmZ h (jn n v).2⟩ := by
    intro n m h v
    apply Subtype.ext
    rw [← hjμ, μ_ιmap, hjμ]
  have hcompat : ∀ n m (h : n ≤ m) (y : Z n), Qn m ⟨y, hmZ h y.2⟩ = Qn n y := by
    intro n m h
    have := DenseRange.equalizer (hcomp n).2.2.2.2
      (g := fun y : Z n => Qn m ⟨y, hmZ h y.2⟩) (h := fun y => Qn n y)
      ((hQnc m).comp (continuous_subtype_val.subtype_mk _)) (hQnc n) ?_
    · exact fun y => congrFun this y
    · funext v
      simp only [Function.comp_apply]
      rw [← hjι n m h v, hQnj, hQnj, Seminorm.comp_apply, Seminorm.comp_apply, μ_ιmap]
  -- gluing
  let N : Y → ℕ := fun y => Nat.find (hexZ y)
  have hN : ∀ y, y ∈ Z (N y) := fun y => Nat.find_spec (hexZ y)
  let Qf : Y → ℝ := fun y => Qn (N y) ⟨y, hN y⟩
  have key : ∀ n (y : Y) (hy : y ∈ Z n), Qf y = Qn n ⟨y, hy⟩ := by
    intro n y hy
    exact (hcompat (N y) n (Nat.find_min' (hexZ y) hy) ⟨y, hN y⟩).symm
  have hadd : ∀ x y, Qf (x + y) ≤ Qf x + Qf y := by
    intro x y
    obtain ⟨a, ha⟩ := hexZ x
    obtain ⟨b, hb⟩ := hexZ y
    have hx : x ∈ Z (max a b) := hmZ (le_max_left a b) ha
    have hy : y ∈ Z (max a b) := hmZ (le_max_right a b) hb
    rw [key _ _ (add_mem hx hy), key _ _ hx, key _ _ hy]
    exact map_add_le_add (Qn (max a b)) ⟨x, hx⟩ ⟨y, hy⟩
  have hsmul : ∀ (c : ℂ) (x : Y), Qf (c • x) = ‖c‖ * Qf x := by
    intro c x
    obtain ⟨a, ha⟩ := hexZ x
    rw [key _ _ (Submodule.smul_mem _ c ha), key _ _ ha]
    exact map_smul_eq_mul (Qn a) c ⟨x, ha⟩
  let Q : Seminorm ℂ Y := Seminorm.of Qf hadd hsmul
  have hQ : ∀ n (y : Z n), Q y = Qn n y := fun n y => key n y y.2
  refine ⟨Q, ?_, ?_⟩
  · refine seminorm_continuous_of_final Z htopZ Q fun n => ?_
    have : (fun y : Z n => Q y) = fun y => Qn n y := funext (hQ n)
    rw [this]
    exact hQnc n
  · intro u
    obtain ⟨n, v, rfl⟩ := exists_μ X₁ X₂ hm₁ hm₂ hex₁ hex₂ u
    rw [hjμ, hQ, hQnj, Seminorm.comp_apply]

/-- Completed inductive tensor products of strict LF-spaces: if `E = lim E_n` and `F = lim F_n` are
strict LF-spaces and the complete space `Y` is the strict inductive limit of subspaces `Y_n`
which are completed projective tensor products `E_n ⊗̂_π F_n` compatibly with `j`, then `(Y, j)`
is a completed inductive tensor product of `E` and `F`. -/
theorem isCompletedIndTensor_of_stages
    (hE : IsHLCS E) (hF : IsHLCS F) (hY : IsHLCS Y) (hYc : IsCompleteTVS Y)
    (X₁ : ℕ → Submodule ℂ E) (X₂ : ℕ → Submodule ℂ F) (Z : ℕ → Submodule ℂ Y)
    (hm₁ : Monotone X₁) (hm₂ : Monotone X₂) (hmZ : Monotone Z)
    (hex₁ : ∀ x, ∃ n, x ∈ X₁ n) (hex₂ : ∀ y, ∃ n, y ∈ X₂ n) (hexZ : ∀ z, ∃ n, z ∈ Z n)
    (hfr₁ : ∀ n, IsFrechet (X₁ n)) (hfr₂ : ∀ n, IsFrechet (X₂ n))
    (htop₁ : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X₁ n) E _ t Subtype.val})
    (htop₂ : ‹TopologicalSpace F› =
      sInf {t | IsLocallyConvexTopology F t ∧ ∀ n, @Continuous (X₂ n) F _ t Subtype.val})
    (htopZ : ‹TopologicalSpace Y› =
      sInf {t | IsLocallyConvexTopology Y t ∧ ∀ n, @Continuous (Z n) Y _ t Subtype.val})
    (j : E ⊗[ℂ] F →ₗ[ℂ] Y) (jn : ∀ n, X₁ n ⊗[ℂ] X₂ n →ₗ[ℂ] Z n)
    (hjn : ∀ n (x : X₁ n) (y : X₂ n), (jn n (x ⊗ₜ[ℂ] y) : Y) = j ((x : E) ⊗ₜ[ℂ] (y : F)))
    (hcomp : ∀ n, IsCompletedProjTensor (X₁ n) (X₂ n) (jn n)) :
    IsCompletedIndTensor E F j := by
  have hTAGY : IsTopologicalAddGroup Y := by
    obtain ⟨ι, _, p, hp⟩ := hY.1
    exact hp.topologicalAddGroup
  have hjμ : ∀ n v, j (μ X₁ X₂ n v) = (jn n v : Y) := by
    intro n v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [μ, hjn]
    | add v w hv hw => rw [map_add, map_add, hv, hw, map_add (jn n)]; rfl
  have hjnc : ∀ n, @Continuous _ _ (projTensorTopology (X₁ n) (X₂ n)) _ (jn n) := by
    intro n
    rw [(hcomp n).2.2.2.1]
    exact continuous_induced_dom
  -- `j` is continuous for the inductive topology
  have hjc : @Continuous _ Y (indTensorTopology E F) _ j := by
    refine (continuous_indTensor_iff E F hE hF Y hY.1 j).2 ⟨fun x => ?_, fun y => ?_⟩
    · refine continuous_of_final X₂ htop₂ hY.1 (j ∘ₗ TensorProduct.mk ℂ E F x) fun n => ?_
      obtain ⟨a, ha⟩ := hex₁ x
      have h1 : a ≤ max a n := le_max_left a n
      have h2 : n ≤ max a n := le_max_right a n
      let x' : X₁ (max a n) := ⟨x, hm₁ h1 ha⟩
      let ι2 : X₂ n → X₂ (max a n) := fun y => ⟨(y : F), hm₂ h2 y.2⟩
      have : (fun y : X₂ n => (j ∘ₗ TensorProduct.mk ℂ E F x) (y : F)) =
          fun y : X₂ n => ((jn (max a n) (x' ⊗ₜ[ℂ] ι2 y) : Z (max a n)) : Y) := by
        funext y
        rw [hjn]
        rfl
      rw [this]
      letI : TopologicalSpace (X₁ (max a n) ⊗[ℂ] X₂ (max a n)) := projTensorTopology _ _
      exact continuous_subtype_val.comp ((hjnc _).comp
        ((continuous_tmul_proj_left _).comp (continuous_subtype_val.subtype_mk _)))
    · refine continuous_of_final X₁ htop₁ hY.1 (j ∘ₗ (TensorProduct.mk ℂ E F).flip y) fun n => ?_
      obtain ⟨a, ha⟩ := hex₂ y
      have h1 : a ≤ max a n := le_max_left a n
      have h2 : n ≤ max a n := le_max_right a n
      let y' : X₂ (max a n) := ⟨y, hm₂ h1 ha⟩
      let ι1 : X₁ n → X₁ (max a n) := fun x => ⟨(x : E), hm₁ h2 x.2⟩
      have : (fun x : X₁ n => (j ∘ₗ (TensorProduct.mk ℂ E F).flip y) (x : E)) =
          fun x : X₁ n => ((jn (max a n) (ι1 x ⊗ₜ[ℂ] y') : Z (max a n)) : Y) := by
        funext x
        rw [hjn]
        rfl
      rw [this]
      letI : TopologicalSpace (X₁ (max a n) ⊗[ℂ] X₂ (max a n)) := projTensorTopology _ _
      exact continuous_subtype_val.comp ((hjnc _).comp
        ((continuous_tmul_proj_right _).comp (continuous_subtype_val.subtype_mk _)))
  refine ⟨hY, hYc, ?_, le_antisymm (continuous_iff_le_induced.1 hjc) ?_, ?_⟩
  · -- injectivity
    intro u w huw
    obtain ⟨a, v, rfl⟩ := exists_μ X₁ X₂ hm₁ hm₂ hex₁ hex₂ u
    obtain ⟨b, v', rfl⟩ := exists_μ X₁ X₂ hm₁ hm₂ hex₁ hex₂ w
    rw [← μ_ιmap X₁ X₂ hm₁ hm₂ (le_max_left a b) v,
      ← μ_ιmap X₁ X₂ hm₁ hm₂ (le_max_right a b) v'] at huw ⊢
    rw [hjμ, hjμ] at huw
    rw [(hcomp (max a b)).2.2.1 (Subtype.ext huw)]
  · -- the induced topology is finer than the inductive one
    obtain ⟨ι, hι, p, hp⟩ := (indTensor_isHLCS E F hE hF).1
    refine le_of_forall_seminorm_continuous _ _ (topologicalAddGroup_induced j) p hp fun i => ?_
    have hpi : @Continuous _ ℝ (indTensorTopology E F) _ (p i) := by
      letI : TopologicalSpace (E ⊗[ℂ] F) := indTensorTopology E F
      exact hp.continuous_seminorm i
    obtain ⟨Q, hQc, hQj⟩ := exists_seminorm_extension hE hF hY X₁ X₂ Z hm₁ hm₂ hmZ hex₁ hex₂
      hexZ hfr₁ hfr₂ htopZ j jn hjμ hcomp (p i) hpi
    have : (p i : E ⊗[ℂ] F → ℝ) = fun u => Q (j u) := funext fun u => (hQj u).symm
    rw [this]
    letI : TopologicalSpace (E ⊗[ℂ] F) := TopologicalSpace.induced j inferInstance
    exact hQc.comp continuous_induced_dom
  · -- dense range
    intro y
    obtain ⟨n, hn⟩ := hexZ y
    have h1 : y ∈ Set.range (Subtype.val : Z n → Y) := ⟨⟨y, hn⟩, rfl⟩
    have h2 := continuous_subtype_val.range_subset_closure_image_dense (hcomp n).2.2.2.2 h1
    refine closure_mono ?_ h2
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨μ X₁ X₂ n v, hjμ n v⟩

end stages

section product

variable {G₁ G₂ : Type u} [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

/-- The product function `(x₁, x₂) ↦ f x₁ * g x₂`, given that it is a Schwartz–Bruhat function. -/
noncomputable def prodFun (hmem : ∀ (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂),
      (fun p : G₁ × G₂ => f p.1 * g p.2) ∈ schwartzBruhatSubmodule (G₁ × G₂))
    (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂) : SchwartzBruhat (G₁ × G₂) :=
  ⟨fun p => f p.1 * g p.2, hmem f g⟩

/-- The bilinear map `(f, g) ↦ f ⊗ g`. -/
noncomputable def prodBil (hmem : ∀ (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂),
      (fun p : G₁ × G₂ => f p.1 * g p.2) ∈ schwartzBruhatSubmodule (G₁ × G₂)) :
    SchwartzBruhat G₁ →ₗ[ℂ] SchwartzBruhat G₂ →ₗ[ℂ] SchwartzBruhat (G₁ × G₂) :=
  LinearMap.mk₂ ℂ (prodFun hmem)
    (fun f f' g => Subtype.ext (funext fun p => by
      show (f p.1 + f' p.1) * g p.2 = f p.1 * g p.2 + f' p.1 * g p.2
      ring))
    (fun c f g => Subtype.ext (funext fun p => by
      show (c * f p.1) * g p.2 = c * (f p.1 * g p.2)
      ring))
    (fun f g g' => Subtype.ext (funext fun p => by
      show f p.1 * (g p.2 + g' p.2) = f p.1 * g p.2 + f p.1 * g' p.2
      ring))
    (fun c f g => Subtype.ext (funext fun p => by
      show f p.1 * (c * g p.2) = c * (f p.1 * g p.2)
      ring))

end product

end Sol_MasulloGRH_schwartzBruhat_prod_isCompletedIndTensor

open Sol_MasulloGRH_schwartzBruhat_prod_isCompletedIndTensor in
open MasulloGRH in
theorem solution
    (G₁ G₂ : Type u) [CommGroup G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁]
    [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] :
    ∃ j : SchwartzBruhat G₁ ⊗[ℂ] SchwartzBruhat G₂ →ₗ[ℂ] SchwartzBruhat (G₁ × G₂),
      (∀ (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂) (p : G₁ × G₂),
        j (f ⊗ₜ[ℂ] g) p = f p.1 * g p.2) ∧
      IsCompletedIndTensor (SchwartzBruhat G₁) (SchwartzBruhat G₂) j := by
  obtain ⟨X₁, X₂, Z, hm₁, hm₂, hmZ, hex₁, hex₂, hexZ, hfr₁, hfr₂, htop₁, htop₂, htopZ, hst⟩ :=
    schwartzBruhat_prod_stages_isCompletedProjTensor G₁ G₂
  choose jn hjn hcomp using hst
  -- the product of two Schwartz–Bruhat functions is a Schwartz–Bruhat function
  have hmem : ∀ (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂),
      (fun p : G₁ × G₂ => f p.1 * g p.2) ∈ schwartzBruhatSubmodule (G₁ × G₂) := by
    intro f g
    obtain ⟨a, ha⟩ := hex₁ f
    obtain ⟨b, hb⟩ := hex₂ g
    have h1 : a ≤ max a b := le_max_left a b
    have h2 : b ≤ max a b := le_max_right a b
    let w : SchwartzBruhat (G₁ × G₂) :=
      (jn (max a b) ((⟨f, hm₁ h1 ha⟩ : X₁ (max a b)) ⊗ₜ[ℂ] (⟨g, hm₂ h2 hb⟩ : X₂ (max a b))) :
        SchwartzBruhat (G₁ × G₂))
    have hw : w.1 = fun p : G₁ × G₂ => f p.1 * g p.2 := funext fun p => hjn _ _ _ p
    rw [← hw]
    exact w.2
  let j : SchwartzBruhat G₁ ⊗[ℂ] SchwartzBruhat G₂ →ₗ[ℂ] SchwartzBruhat (G₁ × G₂) :=
    TensorProduct.lift (prodBil hmem)
  have hj : ∀ (f : SchwartzBruhat G₁) (g : SchwartzBruhat G₂),
      j (f ⊗ₜ[ℂ] g) = prodFun hmem f g := fun f g => by
    show TensorProduct.lift (prodBil hmem) (f ⊗ₜ[ℂ] g) = _
    rw [TensorProduct.lift.tmul]
    rfl
  refine ⟨j, fun f g p => by rw [hj]; rfl, ?_⟩
  have hS₁ := schwartzBruhat_main_structure G₁
  have hS₂ := schwartzBruhat_main_structure G₂
  have hS := schwartzBruhat_main_structure (G₁ × G₂)
  refine isCompletedIndTensor_of_stages hS₁.1 hS₂.1 hS.1 hS.2.2.2.1 X₁ X₂ Z hm₁ hm₂ hmZ
    hex₁ hex₂ hexZ hfr₁ hfr₂ htop₁ htop₂ htopZ j jn ?_ hcomp
  intro n x y
  rw [hj]
  exact Subtype.ext (funext fun p => hjn n x y p)
