-- Prove2me | solution 1 for MvFormalGroup.IsSymmTwoCocycle.addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ee7a0af2-b523-5e54-9b51-373ad0a29cc8

import Mathlib
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Theorems.Thm_MvFormalGroup_existsUnique_eq_subst_nthSeries_of_sub_mem_span
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mFGConnecting

universe u

section PowerSeries

variable {σ R : Type*} [CommRing R]

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem constantCoeff_subst_of_constantCoeff_zero [Finite σ] {τ : Type*}
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, (a i).constantCoeff = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hsplit : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have hz : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  rw [hsplit, subst_add hsa, subst_C, map_add, constantCoeff_C, constantCoeff_subst_eq_zero hsa ha hz,
    add_zero, map_add, constantCoeff_C, hz, add_zero]

theorem injective_of_existsUnique_expansion {A : Type*} [CommRing A] [NoZeroDivisors A]
    [Nontrivial A] (φ : A →+* A) {ι : Type*} [Fintype ι] (b : ι → A)
    (hb : ∀ x : A, ∃! c : ι → A, x = ∑ i, φ (c i) * b i) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨c₁, hc₁, huniq⟩ := hb 1
  have hc₁' : (1 : A) = ∑ i, φ (c₁ i + c * c₁ i) * b i := by
    refine hc₁.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_add, map_mul, hc, zero_mul, add_zero]
  have hcc : (fun i => c₁ i + c * c₁ i) = c₁ := huniq _ hc₁'
  by_contra hne
  have hzero : ∀ i, c₁ i = 0 := fun i => by
    have hi := congrFun hcc i
    have hmul : c * c₁ i = 0 := by
      have := congrArg (fun t => t - c₁ i) hi
      simpa using this
    exact (mul_eq_zero.mp hmul).resolve_left hne
  have : (1 : A) = 0 := by
    rw [hc₁]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, map_zero, zero_mul]
  exact one_ne_zero this

theorem subst_injective_of_finite_quotient {k : Type u} [Field k] {σ : Type} [Fintype σ]
    [DecidableEq σ] (g : σ → MvPowerSeries σ k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries σ k ⧸ Ideal.span (Set.range g))) :
    Function.Injective (subst g : MvPowerSeries σ k → MvPowerSeries σ k) := by

  let d := Fintype.card σ
  let e : σ ≃ Fin d := Fintype.equivFin σ
  let ρ : MvPowerSeries σ k ≃ₐ[k] MvPowerSeries (Fin d) k := renameEquiv k e
  have hρ : ∀ f : MvPowerSeries σ k, ρ f = rename e f := fun f => rfl
  let g' : Fin d → MvPowerSeries (Fin d) k := fun i => ρ (g (e.symm i))
  have hg' : ∀ i, constantCoeff (g' i) = 0 := fun i => by
    show constantCoeff (rename e (g (e.symm i))) = 0
    rw [constantCoeff_rename, hg]
  have hsg : HasSubst g := hasSubst_of_constantCoeff_zero hg
  have hsg' : HasSubst g' := hasSubst_of_constantCoeff_zero hg'

  have hcomm : ∀ f : MvPowerSeries σ k, subst g' (ρ f) = ρ (subst g f) := by
    intro f
    rw [hρ, hρ, rename_eq_subst, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hsg',
      subst_comp_subst_apply hsg (HasSubst.X_comp e)]
    congr 1
    funext s
    show subst g' (X (e s)) = subst (X ∘ e) (g s)
    rw [subst_X hsg']
    show ρ (g (e.symm (e s))) = _
    rw [Equiv.symm_apply_apply, hρ, rename_eq_subst]

  have hIJ : Ideal.span (Set.range g') = (Ideal.span (Set.range g)).map (ρ : MvPowerSeries σ k →+* _) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨g (e.symm i), ⟨e.symm i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨s, rfl⟩, rfl⟩
      exact ⟨e s, by simp [g']⟩
  have hfin' : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g')) :=
    Module.Finite.equiv (Ideal.quotientEquivAlg (Ideal.span (Set.range g)) (Ideal.span (Set.range g'))
      ρ hIJ).toLinearEquiv
  obtain ⟨-, -, b, hb⟩ :=
    MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient g' hg' hfin'
  have hinj := injective_of_existsUnique_expansion (substAlgHom (R := k) hsg').toRingHom b (fun x => by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] using hb x)
  intro x y hxy
  apply ρ.injective
  apply hinj
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom]
  rw [hcomm, hcomm, hxy]

end PowerSeries

section Transport

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

def app {τ : Type*} (a b : Fin n → MvPowerSeries τ k) : Fin n → MvPowerSeries τ k :=
  fun i => subst (Sum.elim a b) (F.toPowerSeries i)

def ev {τ : Type*} (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) (a b : Fin n → MvPowerSeries τ k) :
    MvPowerSeries τ k :=
  subst (Sum.elim a b) Γ

def nth {τ : Type*} (m : ℕ) (a : Fin n → MvPowerSeries τ k) : Fin n → MvPowerSeries τ k :=
  fun i => subst a (F.nthSeries m i)

variable {F}
variable {τ : Type*}

theorem constantCoeff_app {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    ∀ i, (app F a b i).constantCoeff = 0 :=
  MvFormalGroup.constantCoeff_subst_elim F ha hb

theorem constantCoeff_nth (m : ℕ) {a : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) : ∀ i, (nth F m a i).constantCoeff = 0 :=
  fun i => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha
    (MvFormalGroup.constantCoeff_nthSeries F m i)

theorem constantCoeff_zeroFam : ∀ i : Fin n, ((fun _ => (0 : MvPowerSeries τ k)) i).constantCoeff = 0 :=
  fun _ => map_zero _

theorem app_assoc {a b c : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) :
    app F (app F a b) c = app F a (app F b c) :=
  funext fun i => MvFormalGroup.subst_elim_assoc F ha hb hc i

theorem app_comm [F.IsComm] {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    app F a b = app F b a :=
  funext fun i => MvFormalGroup.subst_elim_comm F ha hb i

theorem app_zero_right {a : Fin n → MvPowerSeries τ k} (ha : ∀ i, (a i).constantCoeff = 0) :
    app F a (fun _ => 0) = a :=
  funext fun i => MvFormalGroup.subst_elim_zero_right F ha i

theorem nth_zero (a : Fin n → MvPowerSeries τ k) (ha : ∀ i, (a i).constantCoeff = 0) :
    nth F 0 a = fun _ => 0 := by
  funext i
  show subst a (F.nthSeries 0 i) = 0
  rw [MvFormalGroup.nthSeries_zero]
  show subst a (0 : MvPowerSeries (Fin n) k) = 0
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]

theorem nth_succ (m : ℕ) {a : Fin n → MvPowerSeries τ k} (ha : ∀ i, (a i).constantCoeff = 0) :
    nth F (m + 1) a = app F (nth F m a) a := by
  funext i
  show subst a (F.nthSeries (m + 1) i) = _
  rw [MvFormalGroup.nthSeries_succ]
  show subst a (subst (Sum.elim (F.nthSeries m) fun j => X j) (F.toPowerSeries i)) = _
  rw [MvFormalGroup.subst_subst_elim F (MvFormalGroup.constantCoeff_nthSeries F m)
    (fun j => constantCoeff_X j) (hasSubst_of_constantCoeff_zero ha)]
  show subst (Sum.elim (fun j => subst a (F.nthSeries m j)) fun j => subst a (X j)) (F.toPowerSeries i) = _
  have hX : (fun j => subst a (X j : MvPowerSeries (Fin n) k)) = a :=
    funext fun j => subst_X (hasSubst_of_constantCoeff_zero ha) j
  rw [hX]
  rfl

theorem nth_app [F.IsComm] (m : ℕ) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    nth F m (app F a b) = app F (nth F m a) (nth F m b) := by
  have hXl : HasSubst (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hab : HasSubst (Sum.elim a b) := MvFormalGroup.hasSubst_elim ha hb
  funext i
  have key := MvFormalGroup.Hom.subst_eq (m : MvFormalGroup.End F) i
  rw [MvFormalGroup.End.toPowerSeries_natCast F m] at key
  have key' := congrArg (subst (Sum.elim a b)) key
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab] at key'
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim
    (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
      (MvFormalGroup.constantCoeff_nthSeries F m j))
    (fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
      (MvFormalGroup.constantCoeff_nthSeries F m j))) hab] at key'
  have hfam : (fun s => subst (Sum.elim a b) (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (F.nthSeries m j))
      (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (F.nthSeries m j)) s))
      = Sum.elim (nth F m a) (nth F m b) := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
        (F.nthSeries m j)) = subst a (F.nthSeries m j)
      rw [subst_comp_subst_apply hXl hab]
      congr 1
      funext l
      rw [subst_X hab, Sum.elim_inl]
    · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
        (F.nthSeries m j)) = subst b (F.nthSeries m j)
      rw [subst_comp_subst_apply hXr hab]
      congr 1
      funext l
      rw [subst_X hab, Sum.elim_inr]
  rw [hfam] at key'
  exact key'

variable {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}

theorem ev_add (Γ₁ Γ₂ : MvPowerSeries (Fin n ⊕ Fin n) k) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    ev (Γ₁ + Γ₂) a b = ev Γ₁ a b + ev Γ₂ a b :=
  subst_add (MvFormalGroup.hasSubst_elim ha hb) _ _

theorem ev_cocycle (hΓ : F.IsSymmTwoCocycle Γ) {a b c : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) :
    ev Γ (app F a b) c + ev Γ a b = ev Γ a (app F b c) + ev Γ b c := by
  have hT0 : ∀ s : Fin n ⊕ (Fin n ⊕ Fin n),
      ((Sum.elim a (Sum.elim b c)) s).constantCoeff = 0 := by
    rintro (j | j | j)
    exacts [ha j, hb j, hc j]
  have hT : HasSubst (Sum.elim a (Sum.elim b c)) := hasSubst_of_constantCoeff_zero hT0
  have hzB : ∀ s : Fin n ⊕ Fin n, ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hzC : ∀ s : Fin n ⊕ Fin n, ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hB := hasSubst_of_constantCoeff_zero hzB
  have hC := hasSubst_of_constantCoeff_zero hzC
  have hA : HasSubst (Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
    · exact constantCoeff_X _
  have hA' : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_X _
    · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
  have key := congrArg (subst (R := k) (Sum.elim a (Sum.elim b c))) hΓ.cocycle
  rw [subst_add hT, subst_add hT, subst_comp_subst_apply hA hT, subst_comp_subst_apply hB hT,
    subst_comp_subst_apply hA' hT, subst_comp_subst_apply hC hT] at key
  have hBfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun l => X (Sum.inr (Sum.inl l))) t)) = Sum.elim a b := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hCfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun l => X (Sum.inr (Sum.inr l))) t)) = Sum.elim b c := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hAfam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) s))
      = Sum.elim (app F a b) c := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        = subst (Sum.elim a b) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hB hT, hBfam]
    · simp [subst_X hT]
  have hA'fam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
      = Sum.elim a (app F b c) := by
    funext s
    rcases s with j | j
    · simp [subst_X hT]
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
        = subst (Sum.elim b c) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hC hT, hCfam]
  rw [hAfam, hBfam, hA'fam, hCfam] at key
  exact key

theorem ev_symm (hΓ : F.IsSymmTwoCocycle Γ) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    ev Γ a b = ev Γ b a := by
  have hT : HasSubst (Sum.elim b a) := MvFormalGroup.hasSubst_elim hb ha
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have key := congrArg (subst (R := k) (Sum.elim b a)) hΓ.symm
  rw [subst_comp_subst_apply hswap hT] at key
  have hfam : (fun s => subst (Sum.elim b a) ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
      fun j => X (Sum.inl j)) s)) = Sum.elim a b := by
    funext s
    rcases s with j | j <;> simp [subst_X hT]
  rw [hfam] at key
  show subst (Sum.elim a b) Γ = subst (Sum.elim b a) Γ
  exact key

theorem ev_zero_zero (hΓ : F.IsSymmTwoCocycle Γ) :
    ev Γ (fun _ : Fin n => (0 : MvPowerSeries τ k)) (fun _ => 0) = 0 := by
  have h : (Sum.elim (fun _ : Fin n => (0 : MvPowerSeries τ k)) fun _ => 0) =
      fun _ : Fin n ⊕ Fin n => (0 : MvPowerSeries τ k) := by
    funext s; rcases s with s | s <;> rfl
  show subst (Sum.elim (fun _ : Fin n => (0 : MvPowerSeries τ k)) fun _ => 0) Γ = 0
  rw [h]
  exact MvFormalGroup.subst_zero_of_constantCoeff_eq_zero hΓ.constantCoeff_eq_zero

theorem ev_zero_right (hΓ : F.IsSymmTwoCocycle Γ) {a : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) : ev Γ a (fun _ => 0) = 0 := by
  have h0 := constantCoeff_zeroFam (n := n) (τ := τ) (k := k)
  have key := ev_cocycle hΓ ha h0 h0
  rw [app_zero_right ha, app_zero_right h0, ev_zero_zero hΓ, add_zero] at key

  have := congrArg (fun t => t - ev Γ a (fun _ => 0)) key
  simpa using this

theorem ev_zero_left (hΓ : F.IsSymmTwoCocycle Γ) {b : Fin n → MvPowerSeries τ k}
    (hb : ∀ i, (b i).constantCoeff = 0) : ev Γ (fun _ => 0) b = 0 := by
  rw [ev_symm hΓ (constantCoeff_zeroFam) hb]
  exact ev_zero_right hΓ hb

theorem ev_interchange [F.IsComm] (hΓ : F.IsSymmTwoCocycle Γ) {a b c d : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (hd : ∀ i, (d i).constantCoeff = 0) :
    ev Γ (app F a b) (app F c d) + ev Γ a b + ev Γ c d =
      ev Γ (app F a c) (app F b d) + ev Γ a c + ev Γ b d := by

  have hW : ∀ {b' c' : Fin n → MvPowerSeries τ k}, (∀ i, (b' i).constantCoeff = 0) →
      (∀ i, (c' i).constantCoeff = 0) →
      ev Γ (app F a b') (app F c' d) + ev Γ a b' + ev Γ c' d =
        ev Γ a (app F (app F b' c') d) + ev Γ (app F b' c') d + ev Γ b' c' := by
    intro b' c' hb' hc'
    have h1 := ev_cocycle hΓ ha hb' (constantCoeff_app (F := F) hc' hd)
    have h2 := ev_cocycle hΓ hb' hc' hd
    rw [← app_assoc hb' hc' hd] at h1
    linear_combination h1 - h2
  rw [hW hb hc, hW hc hb, app_comm hc hb, ev_symm hΓ hc hb]

variable (F Γ) in

def phiAt (m : ℕ) (a : Fin n → MvPowerSeries τ k) : MvPowerSeries τ k :=
  ∑ i ∈ Finset.range m, ev Γ (nth F i a) a

theorem phiAt_zero (a : Fin n → MvPowerSeries τ k) : phiAt F Γ 0 a = 0 := by
  simp [phiAt]

theorem phiAt_succ (m : ℕ) (a : Fin n → MvPowerSeries τ k) :
    phiAt F Γ (m + 1) a = phiAt F Γ m a + ev Γ (nth F m a) a := by
  simp [phiAt, Finset.sum_range_succ]

theorem ev_nth_nth [F.IsComm] (hΓ : F.IsSymmTwoCocycle Γ) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) (m : ℕ) :
    ev Γ (nth F m a) (nth F m b) =
      m • ev Γ a b + phiAt F Γ m (app F a b) - phiAt F Γ m a - phiAt F Γ m b := by
  have hab := constantCoeff_app (F := F) ha hb
  induction m with
  | zero =>
    rw [nth_zero a ha, nth_zero b hb, ev_zero_zero hΓ, zero_smul, phiAt_zero, phiAt_zero, phiAt_zero]
    ring
  | succ m ih =>
    have hma := constantCoeff_nth (F := F) m ha
    have hmb := constantCoeff_nth (F := F) m hb
    rw [nth_succ m ha, nth_succ m hb, phiAt_succ, phiAt_succ, phiAt_succ, succ_nsmul]
    have hI := ev_interchange hΓ hma ha hmb hb

    rw [← nth_app m ha hb] at hI
    linear_combination hI + ih

end Transport

section Universal

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

def Xl : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun l => X (Sum.inl l)

def Xr : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun l => X (Sum.inr l)

theorem constantCoeff_Xl : ∀ i, (Xl (n := n) (k := k) i).constantCoeff = 0 :=
  fun _ => constantCoeff_X _

theorem constantCoeff_Xr : ∀ i, (Xr (n := n) (k := k) i).constantCoeff = 0 :=
  fun _ => constantCoeff_X _

theorem elim_Xl_Xr : (Sum.elim Xl Xr : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) = X := by
  funext s; rcases s with l | l <;> rfl

theorem app_Xl_Xr : app F Xl Xr = F.toPowerSeries := by
  funext i
  show subst (Sum.elim Xl Xr) (F.toPowerSeries i) = F.toPowerSeries i
  rw [elim_Xl_Xr, subst_self]
  rfl

theorem ev_Xl_Xr (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) : ev Γ Xl Xr = Γ := by
  show subst (Sum.elim Xl Xr) Γ = Γ
  rw [elim_Xl_Xr, subst_self]
  rfl

variable {F}

theorem subst_phi (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) (m : ℕ) {τ : Type*}
    {a : Fin n → MvPowerSeries τ k} (ha : ∀ i, (a i).constantCoeff = 0) :
    subst a (∑ i ∈ Finset.range m,
      subst (Sum.elim (F.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k)) Γ) = phiAt F Γ m a := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [← coe_substAlgHom hsa, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_substAlgHom hsa]
  show subst a (subst (Sum.elim (F.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k)) Γ) =
    subst (Sum.elim (nth F i a) a) Γ
  rw [subst_comp_subst_apply (MvFormalGroup.hasSubst_elim (MvFormalGroup.constantCoeff_nthSeries F i)
    (fun l => constantCoeff_X l)) hsa]
  congr 1
  funext s
  rcases s with j | j
  · rfl
  · exact subst_X hsa j

end Universal

section Coefficients

variable {k : Type u} [CommRing k] {n : ℕ}

theorem coeff_subst_elim_Xl_zero (G : MvPowerSeries (Fin n ⊕ Fin n) k) (d : Fin n ⊕ Fin n →₀ ℕ)
    (hd : ∀ j, d (Sum.inr j) = 0) :
    coeff d (subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G)
      = coeff d G := by
  classical
  have hθ : HasSubst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    MvFormalGroup.hasSubst_elim constantCoeff_Xl (fun _ => map_zero _)
  rw [coeff_subst hθ]

  have hprod : ∀ e : Fin n ⊕ Fin n →₀ ℕ,
      (e.prod fun s m => (Sum.elim (Xl (n := n) (k := k))
        (fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) s) ^ m) =
        if ∀ j, e (Sum.inr j) = 0 then monomial e 1 else 0 := by
    intro e
    split_ifs with he
    · rw [monomial_one_eq]
      apply Finset.prod_congr rfl
      intro s hs
      rcases s with l | j
      · rfl
      · exact absurd (he j) (Finsupp.mem_support_iff.mp hs)
    · push Not at he
      obtain ⟨j, hj⟩ := he
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hj)
      show (0 : MvPowerSeries (Fin n ⊕ Fin n) k) ^ e (Sum.inr j) = 0
      exact zero_pow hj
  simp only [hprod]
  rw [finsum_eq_single _ d]
  · rw [if_pos hd, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro e hed
    split_ifs with he
    · rw [coeff_monomial, if_neg (Ne.symm hed), smul_zero]
    · rw [map_zero, smul_zero]

theorem exists_eq_sum_Xr_mul (G : MvPowerSeries (Fin n ⊕ Fin n) k)
    (hG : subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G = 0) :
    ∃ q : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k, G = ∑ j, X (Sum.inr j) * q j := by
  classical
  let T : Finset (Fin n ⊕ Fin n) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul T G (by
    intro d hd
    have hd' : ∀ j, d (Sum.inr j) = 0 := fun j => hd (Sum.inr j) (by simp [T])
    rw [← coeff_subst_elim_Xl_zero G d hd', hG, map_zero])
  refine ⟨fun j => q (Sum.inr j), ?_⟩
  rw [hq, Finset.sum_map]
  rfl

end Coefficients

section Injectivity

variable {k : Type u} [Field k] {n : ℕ} (F : MvFormalGroup n k)

theorem subst_elim_nth_Xr_injective (m : ℕ)
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range (F.nthSeries m)))) :
    Function.Injective (subst (Sum.elim (nth F m (Xl (n := n) (k := k))) Xr) :
      MvPowerSeries (Fin n ⊕ Fin n) k → MvPowerSeries (Fin n ⊕ Fin n) k) := by
  classical
  set s₁ : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := Sum.elim (nth F m Xl) Xr with hs₁
  have hs₁0 : ∀ t, constantCoeff (s₁ t) = 0 := by
    rintro (i | i)
    · exact constantCoeff_nth (F := F) m constantCoeff_Xl i
    · exact constantCoeff_X _

  let J₁ : Ideal (MvPowerSeries (Fin n ⊕ Fin n) k) := Ideal.span (Set.range s₁)
  have hXl : HasSubst (Xl (n := n) (k := k)) := hasSubst_of_constantCoeff_zero constantCoeff_Xl
  let φ₁ : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n ⊕ Fin n) k ⧸ J₁ :=
    (Ideal.Quotient.mkₐ k J₁).comp (substAlgHom hXl)
  have hφ₁ : ∀ f, φ₁ f = Ideal.Quotient.mk J₁ (subst Xl f) := fun f => by
    simp [φ₁, coe_substAlgHom]
  have hsurj : Function.Surjective φ₁ := by
    intro y
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨subst (Sum.elim X fun _ => (0 : MvPowerSeries (Fin n) k)) G, ?_⟩
    rw [hφ₁, Ideal.Quotient.eq]

    have hX0 : HasSubst (Sum.elim X fun _ => (0 : MvPowerSeries (Fin n) k)) :=
      MvFormalGroup.hasSubst_elim (fun j => constantCoeff_X j) (fun _ => map_zero _)
    have hcomp : subst Xl (subst (Sum.elim X fun _ => (0 : MvPowerSeries (Fin n) k)) G) =
        subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G := by
      rw [subst_comp_subst_apply hX0 hXl]
      congr 1
      funext t
      rcases t with j | j
      · exact subst_X hXl j
      · show subst Xl (0 : MvPowerSeries (Fin n) k) = 0
        rw [← coe_substAlgHom hXl, map_zero]
    have hkill : subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
        (subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G - G)
        = 0 := by
      have hθ : HasSubst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
        MvFormalGroup.hasSubst_elim constantCoeff_Xl (fun _ => map_zero _)
      rw [subst_sub hθ, subst_comp_subst_apply hθ hθ]
      have hfam : (fun t : Fin n ⊕ Fin n => subst (Sum.elim (Xl (n := n) (k := k))
          fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) (Sum.elim (Xl (n := n) (k := k))
            (fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) t)) =
          Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k) := by
        funext t
        rcases t with j | j
        · exact subst_X hθ (Sum.inl j)
        · show subst _ (0 : MvPowerSeries (Fin n ⊕ Fin n) k) = 0
          rw [← coe_substAlgHom hθ, map_zero]
      rw [hfam, sub_self]
    obtain ⟨q, hq⟩ := exists_eq_sum_Xr_mul _ hkill
    rw [hcomp, hq]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Sum.inr j, ?_⟩)
    rfl
  have hker : ∀ f ∈ Ideal.span (Set.range (F.nthSeries m)), φ₁ f = 0 := by
    have hle : Ideal.span (Set.range (F.nthSeries m)) ≤ RingHom.ker φ₁.toRingHom := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφ₁,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
    intro f hf
    have := hle hf
    rwa [RingHom.mem_ker] at this
  haveI := hfin
  have hfin₁ : Module.Finite k (MvPowerSeries (Fin n ⊕ Fin n) k ⧸ J₁) := by
    refine Module.Finite.of_surjective
      (Ideal.Quotient.liftₐ (Ideal.span (Set.range (F.nthSeries m))) φ₁ hker).toLinearMap ?_
    intro y
    obtain ⟨f, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ f, rfl⟩
  exact subst_injective_of_finite_quotient s₁ hs₁0 hfin₁

theorem subst_elim_nth_nth_injective (m : ℕ)
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range (F.nthSeries m)))) :
    Function.Injective (subst (Sum.elim (nth F m (Xl (n := n) (k := k))) (nth F m Xr)) :
      MvPowerSeries (Fin n ⊕ Fin n) k → MvPowerSeries (Fin n ⊕ Fin n) k) := by
  have h₁ := subst_elim_nth_Xr_injective F m hfin
  have hs₁ : HasSubst (Sum.elim (nth F m (Xl (n := n) (k := k))) Xr) :=
    MvFormalGroup.hasSubst_elim (constantCoeff_nth (F := F) m constantCoeff_Xl) constantCoeff_Xr
  have hs₂ : HasSubst (Sum.elim (Xl (n := n) (k := k)) (nth F m Xr)) :=
    MvFormalGroup.hasSubst_elim constantCoeff_Xl (constantCoeff_nth (F := F) m constantCoeff_Xr)
  have hXl : HasSubst (Xl (n := n) (k := k)) := hasSubst_of_constantCoeff_zero constantCoeff_Xl
  have hXr : HasSubst (Xr (n := n) (k := k)) := hasSubst_of_constantCoeff_zero constantCoeff_Xr

  let sw : MvPowerSeries (Fin n ⊕ Fin n) k ≃ₐ[k] MvPowerSeries (Fin n ⊕ Fin n) k :=
    renameEquiv k (Equiv.sumComm (Fin n) (Fin n))
  have hsw : ∀ f, sw f = subst (Sum.elim (Xr (n := n) (k := k)) Xl) f := by
    intro f
    show rename (Equiv.sumComm (Fin n) (Fin n)) f = _
    rw [rename_eq_subst]
    congr 1
    funext t; rcases t with j | j <;> rfl
  have hswap : HasSubst (Sum.elim (Xr (n := n) (k := k)) Xl) := MvFormalGroup.hasSubst_elim constantCoeff_Xr constantCoeff_Xl

  have hu : (fun t => subst (Sum.elim (nth F m (Xl (n := n) (k := k))) Xr)
      (Sum.elim (Xr (n := n) (k := k)) Xl t)) = Sum.elim Xr (nth F m Xl) := by
    funext t
    rcases t with j | j
    · show subst (Sum.elim (nth F m Xl) Xr) (X (Sum.inr j)) = _
      rw [subst_X hs₁]
      rfl
    · show subst (Sum.elim (nth F m Xl) Xr) (X (Sum.inl j)) = _
      rw [subst_X hs₁]
      rfl
  have hu' : HasSubst (Sum.elim (Xr (n := n) (k := k)) (nth F m Xl)) :=
    MvFormalGroup.hasSubst_elim constantCoeff_Xr (constantCoeff_nth (F := F) m constantCoeff_Xl)
  have hv : (fun t => subst (Sum.elim (Xr (n := n) (k := k)) Xl)
      (Sum.elim (Xr (n := n) (k := k)) (nth F m Xl) t)) = Sum.elim Xl (nth F m Xr) := by
    funext t
    rcases t with j | j
    · show subst (Sum.elim Xr Xl) (X (Sum.inr j)) = _
      rw [subst_X hswap]
      rfl
    · show subst (Sum.elim Xr Xl) (subst Xl (F.nthSeries m j)) = subst Xr (F.nthSeries m j)
      rw [subst_comp_subst_apply hXl hswap]
      congr 1
      funext l
      show subst (Sum.elim Xr Xl) (X (Sum.inl l)) = _
      rw [subst_X hswap]
      rfl
  have hconj : ∀ f : MvPowerSeries (Fin n ⊕ Fin n) k, subst (Sum.elim (Xl (n := n) (k := k)) (nth F m Xr)) f =
      sw (subst (Sum.elim (nth F m (Xl (n := n) (k := k))) Xr) (sw f)) := by
    intro f
    rw [hsw, hsw, subst_comp_subst_apply hswap hs₁, hu, subst_comp_subst_apply hu' hswap, hv]
  have h₂ : Function.Injective (subst (Sum.elim (Xl (n := n) (k := k)) (nth F m Xr)) :
      MvPowerSeries (Fin n ⊕ Fin n) k → MvPowerSeries (Fin n ⊕ Fin n) k) := by
    intro x y hxy
    rw [hconj, hconj] at hxy
    exact sw.injective (h₁ (sw.injective hxy))

  have hcomp : ∀ f : MvPowerSeries (Fin n ⊕ Fin n) k, subst (Sum.elim (nth F m (Xl (n := n) (k := k))) (nth F m Xr)) f =
      subst (Sum.elim (Xl (n := n) (k := k)) (nth F m Xr))
        (subst (Sum.elim (nth F m (Xl (n := n) (k := k))) Xr) f) := by
    intro f
    rw [subst_comp_subst_apply hs₁ hs₂]
    congr 1
    funext t
    rcases t with j | j
    · show subst Xl (F.nthSeries m j) = subst (Sum.elim Xl (nth F m Xr)) (subst Xl (F.nthSeries m j))
      rw [subst_comp_subst_apply hXl hs₂]
      congr 1
      funext l
      show Xl l = subst (Sum.elim Xl (nth F m Xr)) (X (Sum.inl l))
      rw [subst_X hs₂, Sum.elim_inl]
    · show subst Xr (F.nthSeries m j) = subst (Sum.elim Xl (nth F m Xr)) (X (Sum.inr j))
      rw [subst_X hs₂, Sum.elim_inr]
      rfl
  intro x y hxy
  rw [hcomp, hcomp] at hxy
  exact h₁ (h₂ hxy)

end Injectivity

end P2mFGConnecting

universe u

open P2mFGConnecting in
theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} {F₀ : MvFormalGroup n k} [F₀.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h)
    {Γ : MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : F₀.IsSymmTwoCocycle Γ) :
    F₀.addCoboundary (∑ i ∈ Finset.range p,
        MvPowerSeries.subst (Sum.elim (F₀.nthSeries i) fun l => MvPowerSeries.X l) Γ) =
      MvPowerSeries.subst (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (F₀.nthSeries p i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (F₀.nthSeries p i))) Γ ∧
    ((∑ i ∈ Finset.range p,
        MvPowerSeries.subst (Sum.elim (F₀.nthSeries i) fun l => MvPowerSeries.X l) Γ) ∈
        Ideal.span (Set.range (F₀.nthSeries p)) →
      ∃ g : MvPowerSeries (Fin n) k, MvPowerSeries.constantCoeff g = 0 ∧
        Γ = F₀.addCoboundary g) := by
  classical

  set Φ : MvPowerSeries (Fin n) k := ∑ i ∈ Finset.range p,
    MvPowerSeries.subst (Sum.elim (F₀.nthSeries i) fun l => MvPowerSeries.X l) Γ with hΦ
  have hXl0 := constantCoeff_Xl (n := n) (k := k)
  have hXr0 := constantCoeff_Xr (n := n) (k := k)
  have hXl : HasSubst (Xl (n := n) (k := k)) := hasSubst_of_constantCoeff_zero hXl0
  have hXr : HasSubst (Xr (n := n) (k := k)) := hasSubst_of_constantCoeff_zero hXr0
  have hF0 : ∀ i, (F₀.toPowerSeries i).constantCoeff = 0 := F₀.constantCoeff_eq_zero

  have hdbl : (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (F₀.nthSeries p i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (F₀.nthSeries p i)) : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) =
      Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr) := rfl
  have hs : HasSubst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) :=
    MvFormalGroup.hasSubst_elim (constantCoeff_nth (F := F₀) p hXl0) (constantCoeff_nth (F := F₀) p hXr0)

  have hcob : ∀ f : MvPowerSeries (Fin n) k, F₀.addCoboundary f =
      subst (app F₀ Xl Xr) f - subst Xl f - subst Xr f := by
    intro f
    rw [app_Xl_Xr]
    rfl

  have hpart1 : F₀.addCoboundary Φ = subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) Γ := by
    have key := ev_nth_nth (F := F₀) hΓ hXl0 hXr0 p
    rw [ev_Xl_Xr, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul, zero_add,
      ← subst_phi Γ p (constantCoeff_app hXl0 hXr0), ← subst_phi Γ p hXl0,
      ← subst_phi Γ p hXr0] at key
    rw [hcob]
    exact key.symm
  refine ⟨by rw [hdbl]; exact hpart1, ?_⟩

  intro hΦI
  have hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range (F₀.nthSeries p))) :=
    Module.finite_of_finrank_pos (by
      rw [hh]
      exact pow_pos (Fact.out : p.Prime).pos _)

  have hΓ0 : subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) Γ = 0 :=
    ev_zero_right hΓ hXl0
  obtain ⟨q, hq⟩ := exists_eq_sum_Xr_mul Γ hΓ0
  let IY : Ideal (MvPowerSeries (Fin n ⊕ Fin n) k) :=
    Ideal.span (Set.range fun i => MvPowerSeries.subst
      (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (F₀.nthSeries p i))
  have hΓdbl : subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) Γ ∈ IY := by
    rw [hq, ← coe_substAlgHom hs, map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul, coe_substAlgHom hs, subst_X hs, Sum.elim_inr]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

  have hΦY : subst Xr Φ ∈ IY := by
    have h1 : subst Xr Φ ∈ (Ideal.span (Set.range (F₀.nthSeries p))).map (substAlgHom hXr).toRingHom := by
      rw [← coe_substAlgHom hXr]
      exact Ideal.mem_map_of_mem _ hΦI
    rw [Ideal.map_span] at h1
    refine (Ideal.span_le.mpr ?_) h1
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, by simp; rfl⟩

  have hinv : MvPowerSeries.subst F₀.toPowerSeries Φ -
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) Φ ∈ IY := by
    have h1 : MvPowerSeries.subst F₀.toPowerSeries Φ -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) Φ =
        subst Xr Φ + subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) Γ := by
      rw [← hpart1]
      show subst F₀.toPowerSeries Φ - subst Xl Φ =
        subst Xr Φ + (subst F₀.toPowerSeries Φ - subst Xl Φ - subst Xr Φ)
      ring
    rw [h1]
    exact Ideal.add_mem _ hΦY hΓdbl
  obtain ⟨G, hG, -⟩ :=
    MvFormalGroup.existsUnique_eq_subst_nthSeries_of_sub_mem_span F₀ p hfin Φ hinv

  have hnat : HasSubst (F₀.nthSeries p) :=
    hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F₀ p)
  have hpush : F₀.addCoboundary Φ =
      subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) (F₀.addCoboundary G) := by
    rw [hcob, hcob, subst_sub hs, subst_sub hs, hG]
    have e1 : subst (app F₀ Xl Xr) (subst (F₀.nthSeries p) G) =
        subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) (subst (app F₀ Xl Xr) G) := by
      rw [subst_comp_subst_apply hnat (hasSubst_of_constantCoeff_zero (constantCoeff_app hXl0 hXr0)),
        subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (constantCoeff_app hXl0 hXr0)) hs]
      congr 1
      have h2 := nth_app (F := F₀) p hXl0 hXr0

      funext i
      have h3 := congrFun h2 i
      rw [app_Xl_Xr] at h3 ⊢
      exact h3
    have e2 : subst (Xl (n := n) (k := k)) (subst (F₀.nthSeries p) G) =
        subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) (subst (Xl (n := n) (k := k)) G) := by
      rw [subst_comp_subst_apply hnat hXl, subst_comp_subst_apply hXl hs]
      congr 1
      funext i
      show subst Xl (F₀.nthSeries p i) = subst _ (X (Sum.inl i))
      rw [subst_X hs, Sum.elim_inl]
      rfl
    have e3 : subst (Xr (n := n) (k := k)) (subst (F₀.nthSeries p) G) =
        subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) (subst (Xr (n := n) (k := k)) G) := by
      rw [subst_comp_subst_apply hnat hXr, subst_comp_subst_apply hXr hs]
      congr 1
      funext i
      show subst Xr (F₀.nthSeries p i) = subst _ (X (Sum.inr i))
      rw [subst_X hs, Sum.elim_inr]
      rfl
    rw [e1, e2, e3]

  have hzero : subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr)) (Γ - F₀.addCoboundary G) =
      subst (Sum.elim (nth F₀ p (Xl (n := n) (k := k))) (nth F₀ p Xr))
        (0 : MvPowerSeries (Fin n ⊕ Fin n) k) := by
    rw [subst_sub hs, ← hpush, hpart1, sub_self, ← coe_substAlgHom hs, map_zero]
  have hΓG : Γ = F₀.addCoboundary G :=
    sub_eq_zero.mp (subst_elim_nth_nth_injective F₀ p hfin hzero)
  refine ⟨G, ?_, hΓG⟩

  have hΦ0 : constantCoeff Φ = 0 := by
    rw [hΦ, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact constantCoeff_subst_eq_zero
      (MvFormalGroup.hasSubst_elim (MvFormalGroup.constantCoeff_nthSeries F₀ i) fun l => constantCoeff_X l)
      (by rintro (l | l); exacts [MvFormalGroup.constantCoeff_nthSeries F₀ i l, constantCoeff_X l])
      hΓ.constantCoeff_eq_zero
  rw [← hΦ0, hG, constantCoeff_subst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F₀ p)]

end

end S_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
end P2MW
export P2MW.S_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span (solution)
