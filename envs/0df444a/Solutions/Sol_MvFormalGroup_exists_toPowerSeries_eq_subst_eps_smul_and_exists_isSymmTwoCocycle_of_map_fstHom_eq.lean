-- Prove2me | solution 1 for MvFormalGroup.exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a652fc9d-2057-5138-a9e4-a396328b93db

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mFGTranslate

universe u

section General

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {g : ℕ} {τ : Type*}

theorem map_toPowerSeries (F : MvFormalGroup g R) (f : R →+* S) (i : Fin g) :
    (F.map f).toPowerSeries i = MvPowerSeries.map f (F.toPowerSeries i) := rfl

theorem map_toPowerSeries_fun (F : MvFormalGroup g R) (f : R →+* S) :
    (F.map f).toPowerSeries = fun i => MvPowerSeries.map f (F.toPowerSeries i) := rfl

private theorem _root_.P2mFGTranslate.map_map (F : MvFormalGroup g R) (f : R →+* S) (f' : S →+* T) :
    (F.map f).map f' = F.map (f'.comp f) := by
  ext i d
  simp [map_toPowerSeries, MvPowerSeries.map_map]

p2m_export "P2mFGTranslate" "map_map"
private theorem _root_.P2mFGTranslate.map_id (F : MvFormalGroup g R) : F.map (RingHom.id R) = F := by
  ext i d
  simp [map_toPowerSeries]

p2m_export "P2mFGTranslate" "map_id"

theorem isComm_map (F : MvFormalGroup g R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm := by
  constructor
  intro i
  have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
    rintro (j | j) <;> simp [constantCoeff_X]
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  rw [map_subst (hasSubst_of_constantCoeff_zero hz)] at key
  have hfam : (fun s => MvPowerSeries.map f ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp
  rw [hfam] at key
  exact key

theorem map_subst_elim (F : MvFormalGroup g R) (f : R →+* S)
    {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin g) :
    MvPowerSeries.map f (subst (Sum.elim a b) (F.toPowerSeries i)) =
      subst (Sum.elim (fun j => MvPowerSeries.map f (a j)) fun j => MvPowerSeries.map f (b j))
        ((F.map f).toPowerSeries i) := by
  rw [map_subst (MvFormalGroup.hasSubst_elim ha hb), map_toPowerSeries]
  congr 1
  funext s
  rcases s with j | j <;> rfl

theorem map_negSeries (F : MvFormalGroup g R) (f : R →+* S)
    {a : Fin g → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0) :
    (fun i => MvPowerSeries.map f (MvFormalGroup.negSeries F a i)) =
      MvFormalGroup.negSeries (F.map f) fun i => MvPowerSeries.map f (a i) := by
  have hna : ∀ j, (MvFormalGroup.negSeries F a j).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_negSeries F a
  refine MvFormalGroup.negSeries_unique (F.map f)
    (fun j => by rw [constantCoeff_map, ha j, map_zero])
    (fun j => by rw [constantCoeff_map, hna j, map_zero]) fun i => ?_
  rw [← map_subst_elim F f ha hna i, MvFormalGroup.subst_elim_negSeries F ha i, map_zero]

theorem cancel_left (F : MvFormalGroup g R) {w e e' : Fin g → MvPowerSeries τ R}
    (hw : ∀ j, (w j).constantCoeff = 0) (he : ∀ j, (e j).constantCoeff = 0)
    (he' : ∀ j, (e' j).constantCoeff = 0)
    (h : (fun i => subst (Sum.elim w e) (F.toPowerSeries i)) =
      fun i => subst (Sum.elim w e') (F.toPowerSeries i)) :
    e = e' := by
  have hnw : ∀ j, (MvFormalGroup.negSeries F w j).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_negSeries F w
  have aux : ∀ (c : Fin g → MvPowerSeries τ R), (∀ j, (c j).constantCoeff = 0) →
      c = fun i => subst (Sum.elim (MvFormalGroup.negSeries F w) fun j =>
        subst (Sum.elim w c) (F.toPowerSeries j)) (F.toPowerSeries i) := by
    intro c hc
    funext i
    rw [← MvFormalGroup.subst_elim_assoc F hnw hw hc i]
    have hz : (fun j => subst (Sum.elim (MvFormalGroup.negSeries F w) w) (F.toPowerSeries j)) =
        fun _ => (0 : MvPowerSeries τ R) := by
      funext j
      exact MvFormalGroup.subst_elim_negSeries_left F hw j
    rw [hz, MvFormalGroup.subst_elim_zero_left F hc i]
  rw [aux e he, aux e' he', h]

end General

section Dual

variable {k : Type u} [CommRing k] {τ : Type*}

local notation "𝔻" => DualNumber k
local notation "ιk" => TrivSqZeroExt.inlHom k k
set_option quotPrecheck false in
local notation "φk" => (TrivSqZeroExt.fstHom k k k).toRingHom

open DualNumber

theorem fst_comp_inl : (φk).comp (ιk) = RingHom.id k := by
  ext x
  rfl

def sndSeries (Ψ : MvPowerSeries τ (DualNumber k)) : MvPowerSeries τ k :=
  fun d => TrivSqZeroExt.snd (Ψ d)

theorem coeff_sndSeries (Ψ : MvPowerSeries τ 𝔻) (d : τ →₀ ℕ) :
    coeff d (sndSeries Ψ) = TrivSqZeroExt.snd (coeff d Ψ) := rfl

theorem map_fst_lift (q : MvPowerSeries τ k) :
    MvPowerSeries.map φk (MvPowerSeries.map ιk q) = q := by
  rw [MvPowerSeries.map_map, fst_comp_inl, MvPowerSeries.map_id]
  rfl

theorem coeff_eps_smul (Ψ : MvPowerSeries τ 𝔻) (d : τ →₀ ℕ) :
    coeff d ((ε : 𝔻) • Ψ) = ε * coeff d Ψ := rfl

theorem map_fst_eps_smul (Ψ : MvPowerSeries τ 𝔻) :
    MvPowerSeries.map φk ((ε : 𝔻) • Ψ) = 0 := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_map, coeff_eps_smul, map_mul]
  simp

theorem eps_smul_eps_smul (Ψ : MvPowerSeries τ 𝔻) : (ε : 𝔻) • (ε : 𝔻) • Ψ = 0 := by
  rw [smul_smul, eps_mul_eps, zero_smul]

theorem constantCoeff_lift (q : MvPowerSeries τ k) :
    (MvPowerSeries.map ιk q).constantCoeff = TrivSqZeroExt.inl q.constantCoeff :=
  constantCoeff_map _ _

theorem constantCoeff_eps_smul_lift {q : MvPowerSeries τ k} (hq : q.constantCoeff = 0) :
    ((ε : 𝔻) • MvPowerSeries.map ιk q).constantCoeff = 0 := by
  rw [constantCoeff_smul, constantCoeff_lift, hq]
  simp

theorem eq_lift_add_eps_smul (Ψ : MvPowerSeries τ 𝔻) :
    Ψ = MvPowerSeries.map ιk (MvPowerSeries.map φk Ψ) + (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries Ψ) := by
  refine MvPowerSeries.ext fun d => ?_
  rw [map_add, coeff_map, coeff_map, coeff_eps_smul, coeff_map, coeff_sndSeries]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem eq_eps_smul_of_map_fst_eq_zero {Ψ : MvPowerSeries τ 𝔻}
    (h : MvPowerSeries.map φk Ψ = 0) :
    Ψ = (ε : 𝔻) • MvPowerSeries.map ιk (sndSeries Ψ) := by
  conv_lhs => rw [eq_lift_add_eps_smul Ψ, h, map_zero, zero_add]

theorem eps_smul_lift_injective {q q' : MvPowerSeries τ k}
    (h : (ε : 𝔻) • MvPowerSeries.map ιk q = (ε : 𝔻) • MvPowerSeries.map ιk q') : q = q' := by
  refine MvPowerSeries.ext fun d => ?_
  have := congrArg (fun Ψ => TrivSqZeroExt.snd (coeff d Ψ)) h
  simpa [coeff_eps_smul, coeff_map] using this

theorem subst_lift_lift {σ : Type*} {a : σ → MvPowerSeries τ k} (ha : HasSubst a)
    (q : MvPowerSeries σ k) :
    subst (fun s => MvPowerSeries.map ιk (a s)) (MvPowerSeries.map ιk q) =
      MvPowerSeries.map ιk (subst a q) := by
  rw [map_subst ha]

theorem eps_smul_subst_lift {σ : Type*} {a : σ → MvPowerSeries τ 𝔻} (ha : HasSubst a)
    {a₀ : σ → MvPowerSeries τ k} (h : ∀ s, MvPowerSeries.map φk (a s) = a₀ s)
    (q : MvPowerSeries σ k) :
    (ε : 𝔻) • subst a (MvPowerSeries.map ιk q) = (ε : 𝔻) • MvPowerSeries.map ιk (subst a₀ q) := by
  have hfst : MvPowerSeries.map φk (subst a (MvPowerSeries.map ιk q)) = subst a₀ q := by
    rw [map_subst ha, map_fst_lift]
    congr 1
    funext s
    exact h s
  conv_lhs => rw [eq_lift_add_eps_smul (subst a (MvPowerSeries.map ιk q)), hfst, smul_add,
    eps_smul_eps_smul, add_zero]

theorem map_lift_X {σ : Type*} (s : σ) :
    MvPowerSeries.map ιk (X s : MvPowerSeries σ k) = X s := map_X _ _

variable {n : ℕ} (F₀ : MvFormalGroup n k)

set_option quotPrecheck false in

local notation "L" => MvFormalGroup.map (TrivSqZeroExt.inlHom k k) F₀

scoped instance isComm_lift {F₀ : MvFormalGroup n k} [F₀.IsComm] :
    (MvFormalGroup.map (TrivSqZeroExt.inlHom k k) F₀).IsComm :=
  isComm_map F₀ _

theorem lift_toPowerSeries (i : Fin n) :
    (L).toPowerSeries i = MvPowerSeries.map ιk (F₀.toPowerSeries i) := rfl

theorem constantCoeff_L (j : Fin n) : ((L).toPowerSeries j).constantCoeff = 0 :=
  (L).constantCoeff_eq_zero j

theorem map_fst_L : (L).map φk = F₀ := by
  rw [map_map, fst_comp_inl, map_id]

theorem subst_elim_X_X {R : Type*} [CommRing R] (G : MvFormalGroup n R) (i : Fin n) :
    subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
      fun l => X (Sum.inr l)) (G.toPowerSeries i) = G.toPowerSeries i := by
  have hX : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) R))
      fun l => X (Sum.inr l)) = X := by
    funext s
    rcases s with l | l <;> rfl
  rw [hX, subst_self]
  rfl

def tr (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) :
    Fin n → MvPowerSeries (Fin n ⊕ Fin n) 𝔻 :=
  fun i => subst (Sum.elim (L).toPowerSeries
    fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) ((L).toPowerSeries i)

theorem tr_apply (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k) (i : Fin n) :
    tr F₀ Γ i = subst (Sum.elim (L).toPowerSeries
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) ((L).toPowerSeries i) := rfl

theorem map_fst_subst_elim {w v : Fin n → MvPowerSeries τ 𝔻} {w₀ v₀ : Fin n → MvPowerSeries τ k}
    (hw : ∀ j, (w j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0)
    (hw₀ : ∀ j, MvPowerSeries.map φk (w j) = w₀ j) (hv₀ : ∀ j, MvPowerSeries.map φk (v j) = v₀ j)
    (i : Fin n) :
    MvPowerSeries.map φk (subst (Sum.elim w v) ((L).toPowerSeries i)) =
      subst (Sum.elim w₀ v₀) (F₀.toPowerSeries i) := by
  rw [map_subst_elim (L) φk hw hv i, map_fst_L]
  congr 1
  funext s
  rcases s with j | j
  · exact hw₀ j
  · exact hv₀ j

theorem map_fst_subst_elim_eps {w : Fin n → MvPowerSeries τ 𝔻} {w₀ : Fin n → MvPowerSeries τ k}
    (hw : ∀ j, (w j).constantCoeff = 0) (hw₀ : ∀ j, MvPowerSeries.map φk (w j) = w₀ j)
    (hw₀' : ∀ j, (w₀ j).constantCoeff = 0)
    {γ : Fin n → MvPowerSeries τ k} (hγ : ∀ l, (γ l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map φk (subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (γ l))
      ((L).toPowerSeries i)) = w₀ i := by
  rw [map_fst_subst_elim F₀ hw (fun l => constantCoeff_eps_smul_lift (hγ l)) hw₀
    (fun l => map_fst_eps_smul _) i]
  exact MvFormalGroup.subst_elim_zero_right F₀ hw₀' i

theorem map_fst_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    MvPowerSeries.map φk (tr F₀ Γ i) = F₀.toPowerSeries i :=
  map_fst_subst_elim_eps F₀ (constantCoeff_L F₀) (fun j => by rw [lift_toPowerSeries, map_fst_lift])
    F₀.constantCoeff_eq_zero hΓ i

theorem constantCoeff_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    (tr F₀ Γ i).constantCoeff = 0 :=
  MvFormalGroup.constantCoeff_subst_elim (L) (constantCoeff_L F₀)
    (fun l => constantCoeff_eps_smul_lift (hΓ l)) i

theorem subst_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0)
    {P Q : Fin n → MvPowerSeries τ 𝔻} {P₀ Q₀ : Fin n → MvPowerSeries τ k}
    (hP : ∀ j, (P j).constantCoeff = 0) (hQ : ∀ j, (Q j).constantCoeff = 0)
    (hP₀ : ∀ j, MvPowerSeries.map φk (P j) = P₀ j) (hQ₀ : ∀ j, MvPowerSeries.map φk (Q j) = Q₀ j)
    (i : Fin n) :
    subst (Sum.elim P Q) (tr F₀ Γ i) =
      subst (Sum.elim (fun j => subst (Sum.elim P Q) ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim P₀ Q₀) (Γ l)))
        ((L).toPowerSeries i) := by
  have hPQ : HasSubst (Sum.elim P Q) := MvFormalGroup.hasSubst_elim hP hQ
  rw [tr_apply, MvFormalGroup.subst_subst_elim (L) (constantCoeff_L F₀)
    (fun l => constantCoeff_eps_smul_lift (hΓ l)) hPQ i]
  congr 1
  funext s
  rcases s with j | l
  · rfl
  · show subst (Sum.elim P Q) ((ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) =
      (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim P₀ Q₀) (Γ l))
    rw [subst_smul hPQ, eps_smul_subst_lift hPQ (a₀ := Sum.elim P₀ Q₀)]
    rintro (j | j)
    · exact hP₀ j
    · exact hQ₀ j

theorem subst_elim_right_comm {R : Type*} [CommRing R] (G : MvFormalGroup n R) [G.IsComm]
    {σ : Type*} {x e c : Fin n → MvPowerSeries σ R}
    (hx : ∀ j, (x j).constantCoeff = 0) (he : ∀ j, (e j).constantCoeff = 0)
    (hc : ∀ j, (c j).constantCoeff = 0) :
    (fun i => subst (Sum.elim (fun j => subst (Sum.elim x e) (G.toPowerSeries j)) c)
      (G.toPowerSeries i)) =
    fun i => subst (Sum.elim (fun j => subst (Sum.elim x c) (G.toPowerSeries j)) e)
      (G.toPowerSeries i) := by
  funext i
  rw [MvFormalGroup.subst_elim_assoc G hx he hc i, MvFormalGroup.subst_elim_assoc G hx hc he i]
  have hce : (fun j => subst (Sum.elim e c) (G.toPowerSeries j)) =
      fun j => subst (Sum.elim c e) (G.toPowerSeries j) :=
    funext fun j => MvFormalGroup.subst_elim_comm G he hc j
  rw [hce]

theorem eps_pow_eq_zero {m : ℕ} (hm : 2 ≤ m) : (ε : 𝔻) ^ m = 0 :=
  pow_eq_zero_of_le hm eps_pow_two

theorem finsuppProd_eps_smul_eq_zero {σ : Type*} (w : σ → MvPowerSeries τ 𝔻)
    {d : σ →₀ ℕ} (hd : 2 ≤ d.degree) :
    (d.prod fun s m => ((ε : 𝔻) • w s) ^ m) = 0 := by
  classical
  have h1 : (d.prod fun s m => ((ε : 𝔻) • w s) ^ m) =
      (d.prod fun s m => (MvPowerSeries.C (ε : 𝔻) : MvPowerSeries τ 𝔻) ^ m) *
        d.prod fun s m => (w s) ^ m := by
    unfold Finsupp.prod
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    show ((ε : 𝔻) • w s) ^ (d s) = (MvPowerSeries.C (ε : 𝔻)) ^ (d s) * (w s) ^ (d s)
    rw [smul_eq_C_mul, mul_pow]
  have h2 : (d.prod fun s m => (MvPowerSeries.C (ε : 𝔻) : MvPowerSeries τ 𝔻) ^ m) = 0 := by
    unfold Finsupp.prod
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, ← map_pow, eps_pow_eq_zero hd,
      map_zero]
  rw [h1, h2, zero_mul]

theorem subst_elim_eps_eps {u v : Fin n → MvPowerSeries τ k}
    (hu : ∀ j, (u j).constantCoeff = 0) (hv : ∀ j, (v j).constantCoeff = 0) (i : Fin n) :
    subst (Sum.elim (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j))
      fun j => (ε : 𝔻) • MvPowerSeries.map ιk (v j)) ((L).toPowerSeries i) =
      (ε : 𝔻) • MvPowerSeries.map ιk (u i + v i) := by
  classical
  set c : Fin n ⊕ Fin n → MvPowerSeries τ 𝔻 := Sum.elim
    (fun j => (ε : 𝔻) • MvPowerSeries.map ιk (u j))
    fun j => (ε : 𝔻) • MvPowerSeries.map ιk (v j) with hc
  have hc0 : ∀ s, (c s).constantCoeff = 0 := by
    rintro (j | j)
    · exact constantCoeff_eps_smul_lift (hu j)
    · exact constantCoeff_eps_smul_lift (hv j)
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0

  set w : Fin n ⊕ Fin n → MvPowerSeries τ 𝔻 := Sum.elim
    (fun j => MvPowerSeries.map ιk (u j)) fun j => MvPowerSeries.map ιk (v j) with hw
  have hcw : ∀ s, c s = (ε : 𝔻) • w s := by
    rintro (j | j) <;> rfl
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_subst hsc,
    finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun s : Fin n ⊕ Fin n => Finsupp.single s 1) (fun d hd => ?_),
    Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective one_ne_zero hab)]
  · have hterm : ∀ s : Fin n ⊕ Fin n,
        coeff (Finsupp.single s 1) ((L).toPowerSeries i) •
          coeff e ((Finsupp.single s 1).prod fun s' m => (c s') ^ m) =
        coeff (Finsupp.single s 1) ((L).toPowerSeries i) * coeff e (c s) := by
      intro s
      rw [Finsupp.prod_single_index (h := fun s' m => (c s') ^ m) (pow_zero (c s)), pow_one,
        smul_eq_mul]
    simp only [hterm]
    rw [Fintype.sum_sum_type]
    simp only [lift_toPowerSeries, coeff_map, F₀.coeff_single_inl, F₀.coeff_single_inr]
    simp only [apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    show coeff e (c (Sum.inl i)) + coeff e (c (Sum.inr i)) = _
    rw [hc]
    simp only [Sum.elim_inl, Sum.elim_inr, map_add, smul_add]
  ·
    by_contra hmem
    apply hd
    rcases Nat.lt_trichotomy d.degree 1 with hlt | heq | hgt
    · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      subst hd0
      rw [coeff_zero_eq_constantCoeff_apply, (L).constantCoeff_eq_zero i, zero_smul]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = d := by
        have hmem' : d ∈ {d' : Fin n ⊕ Fin n →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmem
    · have hz : (d.prod fun s' m => (c s') ^ m) = 0 := by
        have : (d.prod fun s' m => (c s') ^ m) = d.prod fun s' m => ((ε : 𝔻) • w s') ^ m :=
          Finsupp.prod_congr fun s' _ => by rw [hcw]
        rw [this]
        exact finsuppProd_eps_smul_eq_zero w (by omega)
      rw [hz, map_zero, smul_zero]

theorem subst_elim_eps_assoc [F₀.IsComm] {w : Fin n → MvPowerSeries τ 𝔻}
    (hw : ∀ j, (w j).constantCoeff = 0) {a b : Fin n → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    (fun i => subst (Sum.elim (fun j => subst
        (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l)) ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries i)) =
    fun i => subst (Sum.elim w fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l + b l))
      ((L).toPowerSeries i) := by
  funext i
  rw [MvFormalGroup.subst_elim_assoc (L) hw (fun l => constantCoeff_eps_smul_lift (ha l))
    (fun l => constantCoeff_eps_smul_lift (hb l)) i]
  have hin : (fun j => subst (Sum.elim (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (b l)) ((L).toPowerSeries j)) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (a l + b l) :=
    funext fun j => subst_elim_eps_eps F₀ ha hb j
  rw [hin]

section Assoc

set_option quotPrecheck false in
local notation "V₃" => MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) (DualNumber k)
set_option quotPrecheck false in
local notation "V₃₀" => MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k
set_option quotPrecheck false in
local notation "𝔸" => (fun l : Fin n => (X (Sum.inl l) : V₃))
set_option quotPrecheck false in
local notation "𝔹" => (fun l : Fin n => (X (Sum.inr (Sum.inl l)) : V₃))
set_option quotPrecheck false in
local notation "ℂ'" => (fun l : Fin n => (X (Sum.inr (Sum.inr l)) : V₃))
set_option quotPrecheck false in
local notation "𝔸₀" => (fun l : Fin n => (X (Sum.inl l) : V₃₀))
set_option quotPrecheck false in
local notation "𝔹₀" => (fun l : Fin n => (X (Sum.inr (Sum.inl l)) : V₃₀))
set_option quotPrecheck false in
local notation "ℂ₀" => (fun l : Fin n => (X (Sum.inr (Sum.inr l)) : V₃₀))

theorem cX {R : Type*} [CommRing R] {σ : Type*} (f : Fin n → σ) :
    ∀ l : Fin n, ((fun l => (X (f l) : MvPowerSeries σ R)) l).constantCoeff = 0 :=
  fun l => constantCoeff_X _

theorem map_fst_X {σ : Type*} (f : Fin n → σ) :
    ∀ l : Fin n, MvPowerSeries.map φk ((fun l => (X (f l) : MvPowerSeries σ 𝔻)) l) =
      (fun l => (X (f l) : MvPowerSeries σ k)) l :=
  fun l => map_X _ _

variable {F₀}

theorem assoc_lhs [F₀.IsComm] {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    subst (Sum.elim (fun j => subst (Sum.elim 𝔸 𝔹) (tr F₀ Γ j)) ℂ') (tr F₀ Γ i) =
      subst (Sum.elim
        (fun j => subst (Sum.elim (fun j' => subst (Sum.elim 𝔸 𝔹) ((L).toPowerSeries j')) ℂ')
          ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (Sum.elim (fun j => subst (Sum.elim 𝔸₀ 𝔹₀) (F₀.toPowerSeries j)) ℂ₀) (Γ l) +
            subst (Sum.elim 𝔸₀ 𝔹₀) (Γ l)))
        ((L).toPowerSeries i) := by

  have hΓAB : ∀ l, (subst (Sum.elim 𝔸₀ 𝔹₀) (Γ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim (cX _) (cX _))
      (by rintro (j | j) <;> exact constantCoeff_X _) (hΓ l)
  have hFAB : ∀ j, (subst (Sum.elim 𝔸₀ 𝔹₀) (F₀.toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim F₀ (cX _) (cX _)
  have hΓFC : ∀ l, (subst (Sum.elim (fun j => subst (Sum.elim 𝔸₀ 𝔹₀) (F₀.toPowerSeries j)) ℂ₀)
      (Γ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hFAB (cX _))
      (by rintro (j | j); exacts [hFAB j, constantCoeff_X _]) (hΓ l)
  have hLAB : ∀ j, (subst (Sum.elim 𝔸 𝔹) ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) (cX _) (cX _)

  have hP : (fun j => subst (Sum.elim 𝔸 𝔹) (tr F₀ Γ j)) =
      fun j => subst (Sum.elim (fun j' => subst (Sum.elim 𝔸 𝔹) ((L).toPowerSeries j'))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔸₀ 𝔹₀) (Γ l)))
        ((L).toPowerSeries j) :=
    funext fun j => subst_tr F₀ hΓ (cX _) (cX _) (map_fst_X _) (map_fst_X _) j
  rw [hP]

  have hPred : ∀ j, MvPowerSeries.map φk (subst (Sum.elim
      (fun j' => subst (Sum.elim 𝔸 𝔹) ((L).toPowerSeries j'))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔸₀ 𝔹₀) (Γ l)))
      ((L).toPowerSeries j)) = subst (Sum.elim 𝔸₀ 𝔹₀) (F₀.toPowerSeries j) :=
    map_fst_subst_elim_eps F₀ hLAB
      (fun j => map_fst_subst_elim F₀ (cX _) (cX _) (map_fst_X _) (map_fst_X _) j) hFAB hΓAB
  have hPc : ∀ j, (subst (Sum.elim
      (fun j' => subst (Sum.elim 𝔸 𝔹) ((L).toPowerSeries j'))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔸₀ 𝔹₀) (Γ l)))
      ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hLAB (fun l => constantCoeff_eps_smul_lift (hΓAB l))
  rw [subst_tr F₀ hΓ hPc (cX _) hPred (map_fst_X _) i]

  rw [subst_elim_right_comm (L) hLAB (fun l => constantCoeff_eps_smul_lift (hΓAB l)) (cX _)]

  have hLABC : ∀ j, (subst (Sum.elim (fun j' => subst (Sum.elim 𝔸 𝔹) ((L).toPowerSeries j')) ℂ')
      ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hLAB (cX _)
  have key := congrFun (subst_elim_eps_assoc F₀ hLABC hΓAB hΓFC) i
  simp only at key
  rw [key]
  refine congrArg (fun c => subst (Sum.elim _ c) ((L).toPowerSeries i)) (funext fun l => ?_)
  rw [add_comm]

theorem assoc_rhs [F₀.IsComm] {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, (Γ l).constantCoeff = 0) (i : Fin n) :
    subst (Sum.elim 𝔸 fun j => subst (Sum.elim 𝔹 ℂ') (tr F₀ Γ j)) (tr F₀ Γ i) =
      subst (Sum.elim
        (fun j => subst (Sum.elim 𝔸 fun j' => subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j'))
          ((L).toPowerSeries j))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk
          (subst (Sum.elim 𝔸₀ fun j => subst (Sum.elim 𝔹₀ ℂ₀) (F₀.toPowerSeries j)) (Γ l) +
            subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)))
        ((L).toPowerSeries i) := by
  have hΓBC : ∀ l, (subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim (cX _) (cX _))
      (by rintro (j | j) <;> exact constantCoeff_X _) (hΓ l)
  have hFBC : ∀ j, (subst (Sum.elim 𝔹₀ ℂ₀) (F₀.toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim F₀ (cX _) (cX _)
  have hΓAF : ∀ l, (subst (Sum.elim 𝔸₀ fun j => subst (Sum.elim 𝔹₀ ℂ₀) (F₀.toPowerSeries j))
      (Γ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim (cX _) hFBC)
      (by rintro (j | j); exacts [constantCoeff_X _, hFBC j]) (hΓ l)
  have hLBC : ∀ j, (subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) (cX _) (cX _)

  have hP : (fun j => subst (Sum.elim 𝔹 ℂ') (tr F₀ Γ j)) =
      fun j => subst (Sum.elim (fun j' => subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j'))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)))
        ((L).toPowerSeries j) :=
    funext fun j => subst_tr F₀ hΓ (cX _) (cX _) (map_fst_X _) (map_fst_X _) j
  rw [hP]

  have hPred : ∀ j, MvPowerSeries.map φk (subst (Sum.elim
      (fun j' => subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j'))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)))
      ((L).toPowerSeries j)) = subst (Sum.elim 𝔹₀ ℂ₀) (F₀.toPowerSeries j) :=
    map_fst_subst_elim_eps F₀ hLBC
      (fun j => map_fst_subst_elim F₀ (cX _) (cX _) (map_fst_X _) (map_fst_X _) j) hFBC hΓBC
  have hPc : ∀ j, (subst (Sum.elim
      (fun j' => subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j'))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)))
      ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hLBC (fun l => constantCoeff_eps_smul_lift (hΓBC l))
  rw [subst_tr F₀ hΓ (cX _) hPc (map_fst_X _) hPred i]

  have hin : (fun j => subst (Sum.elim 𝔸 fun j' => subst (Sum.elim
      (fun j'' => subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j''))
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)))
      ((L).toPowerSeries j')) ((L).toPowerSeries j)) =
      fun j => subst (Sum.elim (fun j' => subst (Sum.elim 𝔸 fun j'' =>
        subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j'')) ((L).toPowerSeries j'))
        fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim 𝔹₀ ℂ₀) (Γ l)))
        ((L).toPowerSeries j) :=
    funext fun j => (MvFormalGroup.subst_elim_assoc (L) (cX _) hLBC
      (fun l => constantCoeff_eps_smul_lift (hΓBC l)) j).symm
  rw [hin]

  have hLABC : ∀ j, (subst (Sum.elim 𝔸 fun j' => subst (Sum.elim 𝔹 ℂ') ((L).toPowerSeries j'))
      ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) (cX _) hLBC
  have key := congrFun (subst_elim_eps_assoc F₀ hLABC hΓBC hΓAF) i
  simp only at key
  rw [key]
  refine congrArg (fun c => subst (Sum.elim _ c) ((L).toPowerSeries i)) (funext fun l => ?_)
  rw [add_comm]

end Assoc

section Law

set_option quotPrecheck false in
local notation "V₃" => MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) (DualNumber k)
set_option quotPrecheck false in
local notation "V₃₀" => MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k

variable {F₀}

theorem subst_elim_X_zero_of_isSymmTwoCocycle {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : F₀.IsSymmTwoCocycle Γ) :
    subst (Sum.elim (fun l => (X l : MvPowerSeries (Fin n) k)) fun _ => 0) Γ = 0 := by

  set κ : Fin n ⊕ (Fin n ⊕ Fin n) → MvPowerSeries (Fin n) k :=
    Sum.elim (fun l => X l) (Sum.elim (fun _ => 0) fun _ => 0) with hκ
  have hκ0 : ∀ s, (κ s).constantCoeff = 0 := by
    rintro (l | l | l)
    · exact constantCoeff_X _
    · exact map_zero _
    · exact map_zero _
  have hsκ : HasSubst κ := hasSubst_of_constantCoeff_zero hκ0
  have hA : ∀ l : Fin n, ((X (Sum.inl l) : V₃₀)).constantCoeff = 0 := fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : V₃₀)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : V₃₀)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hX0 : ∀ l : Fin n, ((X l : MvPowerSeries (Fin n) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hz : ∀ _l : Fin n, (0 : MvPowerSeries (Fin n) k).constantCoeff = 0 := fun _ => map_zero _
  have hFAB : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inl l) : V₃₀))
      fun l => X (Sum.inr (Sum.inl l))) (F₀.toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : V₃₀))
      fun l => X (Sum.inr (Sum.inr l))) (F₀.toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  have hκX : ∀ l, subst κ (X (Sum.inl l) : V₃₀) = X l := fun l => by
    rw [subst_X hsκ, hκ, Sum.elim_inl]
  have hκY : ∀ l, subst κ (X (Sum.inr (Sum.inl l)) : V₃₀) = 0 := fun l => by
    rw [subst_X hsκ, hκ, Sum.elim_inr, Sum.elim_inl]
  have hκZ : ∀ l, subst κ (X (Sum.inr (Sum.inr l)) : V₃₀) = 0 := fun l => by
    rw [subst_X hsκ, hκ, Sum.elim_inr, Sum.elim_inr]
  have key := congrArg (subst κ) hΓ.cocycle
  rw [← coe_substAlgHom hsκ, map_add, map_add, coe_substAlgHom hsκ,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hFAB hC) hsκ,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hA hB) hsκ,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hA hFBC) hsκ,
    subst_comp_subst_apply (MvFormalGroup.hasSubst_elim hB hC) hsκ] at key

  have hF1 : ∀ j, subst κ (subst (Sum.elim (fun l => (X (Sum.inl l) : V₃₀))
      fun l => X (Sum.inr (Sum.inl l))) (F₀.toPowerSeries j)) = X j := by
    intro j
    rw [MvFormalGroup.subst_subst_elim F₀ hA hB hsκ j]
    have : (Sum.elim (fun j' => subst κ ((X (Sum.inl j') : V₃₀)))
        fun j' => subst κ ((X (Sum.inr (Sum.inl j')) : V₃₀))) =
        Sum.elim (fun j' => (X j' : MvPowerSeries (Fin n) k)) fun _ => 0 := by
      funext s'
      rcases s' with j' | j'
      · exact hκX j'
      · exact hκY j'
    rw [this, MvFormalGroup.subst_elim_X_zero F₀ j]
  have hF2 : ∀ j, subst κ (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : V₃₀))
      fun l => X (Sum.inr (Sum.inr l))) (F₀.toPowerSeries j)) = 0 := by
    intro j
    rw [MvFormalGroup.subst_subst_elim F₀ hB hC hsκ j]
    have : (Sum.elim (fun j' => subst κ ((X (Sum.inr (Sum.inl j')) : V₃₀)))
        fun j' => subst κ ((X (Sum.inr (Sum.inr j')) : V₃₀))) =
        Sum.elim (fun _ => (0 : MvPowerSeries (Fin n) k)) fun _ => 0 := by
      funext s'
      rcases s' with j' | j'
      · exact hκY j'
      · exact hκZ j'
    rw [this]
    exact MvFormalGroup.subst_elim_zero_right F₀ hz j
  have e1 : (fun s => subst κ (Sum.elim (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : V₃₀))
      fun l => X (Sum.inr (Sum.inl l))) (F₀.toPowerSeries j)) (fun j => X (Sum.inr (Sum.inr j))) s)) =
      Sum.elim (fun l => (X l : MvPowerSeries (Fin n) k)) fun _ => 0 := by
    funext s
    rcases s with j | j
    · exact hF1 j
    · exact hκZ j
  have e2 : (fun s => subst κ (Sum.elim (fun l => (X (Sum.inl l) : V₃₀))
      (fun l => X (Sum.inr (Sum.inl l))) s)) =
      Sum.elim (fun l => (X l : MvPowerSeries (Fin n) k)) fun _ => 0 := by
    funext s
    rcases s with j | j
    · exact hκX j
    · exact hκY j
  have e3 : (fun s => subst κ (Sum.elim (fun l => (X (Sum.inl l) : V₃₀))
      (fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : V₃₀))
        fun l => X (Sum.inr (Sum.inr l))) (F₀.toPowerSeries j)) s)) =
      Sum.elim (fun l => (X l : MvPowerSeries (Fin n) k)) fun _ => 0 := by
    funext s
    rcases s with j | j
    · exact hκX j
    · exact hF2 j
  have e4 : (fun s => subst κ (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : V₃₀))
      (fun l => X (Sum.inr (Sum.inr l))) s)) = fun _ => (0 : MvPowerSeries (Fin n) k) := by
    funext s
    rcases s with j | j
    · exact hκY j
    · exact hκZ j
  rw [e1, e2, e3, e4, MvFormalGroup.subst_zero_of_constantCoeff_eq_zero hΓ.constantCoeff_eq_zero]
    at key
  exact add_left_cancel key

theorem subst_elim_zero_X_of_isSymmTwoCocycle {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : F₀.IsSymmTwoCocycle Γ) :
    subst (Sum.elim (fun _ => 0) fun l => (X l : MvPowerSeries (Fin n) k)) Γ = 0 := by
  have h0X : HasSubst (Sum.elim (fun _ => 0) fun l => (X l : MvPowerSeries (Fin n) k)) :=
    MvFormalGroup.hasSubst_elim (fun _ => map_zero _) fun l => constantCoeff_X _
  have hsw : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)
  conv_lhs => rw [← hΓ.symm]
  rw [subst_comp_subst_apply hsw h0X]
  have hfam : (fun s => subst (Sum.elim (fun _ => 0) fun l => (X l : MvPowerSeries (Fin n) k))
      (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
        (fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun l => (X l : MvPowerSeries (Fin n) k)) fun _ => 0 := by
    funext s
    rcases s with j | j
    · rw [Sum.elim_inl, subst_X h0X, Sum.elim_inr, Sum.elim_inl]
    · rw [Sum.elim_inr, subst_X h0X, Sum.elim_inl, Sum.elim_inr]
  rw [hfam]
  exact subst_elim_X_zero_of_isSymmTwoCocycle hΓ

theorem coeff_single_eq_zero_of_isSymmTwoCocycle {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : F₀.IsSymmTwoCocycle Γ) (s : Fin n ⊕ Fin n) :
    coeff (Finsupp.single s 1) Γ = 0 := by
  classical
  rcases s with j | j
  · have h := congrArg (coeff (Finsupp.single j 1)) (subst_elim_X_zero_of_isSymmTwoCocycle hΓ)
    rw [map_zero, MvFormalGroup.coeff_single_subst
      (by rintro (l | l); exacts [constantCoeff_X _, map_zero _]) Γ j,
      Fintype.sum_sum_type] at h
    simpa [coeff_index_single_X, Finset.sum_ite_eq'] using h
  · have h := congrArg (coeff (Finsupp.single j 1)) (subst_elim_zero_X_of_isSymmTwoCocycle hΓ)
    rw [map_zero, MvFormalGroup.coeff_single_subst
      (by rintro (l | l); exacts [map_zero _, constantCoeff_X _]) Γ j,
      Fintype.sum_sum_type] at h
    simpa [coeff_index_single_X, Finset.sum_ite_eq'] using h

theorem coeff_single_tr {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, F₀.IsSymmTwoCocycle (Γ l)) (i : Fin n) (s : Fin n ⊕ Fin n) :
    coeff (Finsupp.single s 1) (tr F₀ Γ i) = coeff (Finsupp.single s 1) ((L).toPowerSeries i) := by
  classical
  have hfam : ∀ s', (Sum.elim (L).toPowerSeries
      (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l)) s').constantCoeff = 0 := by
    rintro (j | l)
    · exact constantCoeff_L F₀ j
    · exact constantCoeff_eps_smul_lift (hΓ l).constantCoeff_eq_zero
  rw [tr_apply, MvFormalGroup.coeff_single_subst hfam _ s, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, lift_toPowerSeries, coeff_map, F₀.coeff_single_inl,
    F₀.coeff_single_inr, apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, coeff_eps_smul,
    coeff_single_eq_zero_of_isSymmTwoCocycle (hΓ i), mul_zero, add_zero]

variable (F₀) in

def defoLaw [F₀.IsComm] (Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k)
    (hΓ : ∀ l, F₀.IsSymmTwoCocycle (Γ l)) : MvFormalGroup n 𝔻 where
  toPowerSeries := tr F₀ Γ
  constantCoeff_eq_zero := constantCoeff_tr F₀ fun l => (hΓ l).constantCoeff_eq_zero
  coeff_single_inl := by
    intro i j
    rw [coeff_single_tr hΓ i (Sum.inl j)]
    exact (L).coeff_single_inl i j
  coeff_single_inr := by
    intro i j
    rw [coeff_single_tr hΓ i (Sum.inr j)]
    exact (L).coeff_single_inr i j
  assoc := by
    intro i
    have hΓ0 : ∀ l, (Γ l).constantCoeff = 0 := fun l => (hΓ l).constantCoeff_eq_zero
    rw [assoc_lhs hΓ0 i, assoc_rhs hΓ0 i]
    have hA : ∀ l : Fin n, ((X (Sum.inl l) : V₃)).constantCoeff = 0 := fun l => constantCoeff_X _
    have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : V₃)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : V₃)).constantCoeff = 0 :=
      fun l => constantCoeff_X _
    have h3 : (fun j => subst (Sum.elim (fun j' => subst (Sum.elim (fun l : Fin n => (X (Sum.inl l) : V₃))
        fun l : Fin n => (X (Sum.inr (Sum.inl l)) : V₃)) ((L).toPowerSeries j'))
        fun l : Fin n => (X (Sum.inr (Sum.inr l)) : V₃)) ((L).toPowerSeries j)) =
        fun j => subst (Sum.elim (fun l : Fin n => (X (Sum.inl l) : V₃)) fun j' =>
          subst (Sum.elim (fun l : Fin n => (X (Sum.inr (Sum.inl l)) : V₃))
            fun l : Fin n => (X (Sum.inr (Sum.inr l)) : V₃)) ((L).toPowerSeries j'))
          ((L).toPowerSeries j) :=
      funext fun j => MvFormalGroup.subst_elim_assoc (L) hA hB hC j
    rw [h3]
    refine congrArg (fun c => subst (Sum.elim _ c) ((L).toPowerSeries i)) (funext fun l => ?_)
    rw [(hΓ l).cocycle]

theorem defoLaw_comm [F₀.IsComm] {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, F₀.IsSymmTwoCocycle (Γ l)) (i : Fin n) :
    subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
      fun j => X (Sum.inl j)) (tr F₀ Γ i) = tr F₀ Γ i := by
  have hΓ0 : ∀ l, (Γ l).constantCoeff = 0 := fun l => (hΓ l).constantCoeff_eq_zero
  rw [subst_tr F₀ hΓ0 (fun j => constantCoeff_X _) (fun j => constantCoeff_X _)
    (P₀ := fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
    (Q₀ := fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ Fin n) k))
    (fun j => map_X _ _) (fun j => map_X _ _) i, tr_apply]
  refine congrArg (fun c => subst c ((L).toPowerSeries i)) ?_
  refine congrArg₂ Sum.elim (funext fun j => ?_) (funext fun l => ?_)
  · exact MvFormalGroup.IsComm.comm (F := L) j
  · rw [(hΓ l).symm]

theorem isComm_defoLaw [F₀.IsComm] {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, F₀.IsSymmTwoCocycle (Γ l)) : (defoLaw F₀ Γ hΓ).IsComm :=
  ⟨defoLaw_comm hΓ⟩

theorem map_fst_defoLaw [F₀.IsComm] {Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k}
    (hΓ : ∀ l, F₀.IsSymmTwoCocycle (Γ l)) : (defoLaw F₀ Γ hΓ).map φk = F₀ := by
  refine MvFormalGroup.ext (funext fun i => ?_)
  exact map_fst_tr F₀ (fun l => (hΓ l).constantCoeff_eq_zero) i

theorem exists_isSymmTwoCocycle_of_map_fst_eq [F₀.IsComm] (F : MvFormalGroup n 𝔻) [F.IsComm]
    (hF : F.map φk = F₀) :
    ∃ Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k,
      (∀ l, F₀.IsSymmTwoCocycle (Γ l)) ∧ F.toPowerSeries = tr F₀ Γ := by
  have hF0 : ∀ j, (F.toPowerSeries j).constantCoeff = 0 := F.constantCoeff_eq_zero
  have hFred : ∀ j, MvPowerSeries.map φk (F.toPowerSeries j) = F₀.toPowerSeries j := fun j => by
    rw [← map_toPowerSeries, hF]

  set N : Fin n → MvPowerSeries (Fin n ⊕ Fin n) 𝔻 :=
    MvFormalGroup.negSeries (L) (L).toPowerSeries with hN
  have hN0 : ∀ j, (N j).constantCoeff = 0 := MvFormalGroup.constantCoeff_negSeries _ _
  have hNred : ∀ j, MvPowerSeries.map φk (N j) =
      MvFormalGroup.negSeries F₀ F₀.toPowerSeries j := by
    intro j
    have h := congrFun (map_negSeries (L) φk (constantCoeff_L F₀)) j
    rw [hN, h, map_fst_L]
    have hfam : (fun i => MvPowerSeries.map φk ((L).toPowerSeries i)) = F₀.toPowerSeries :=
      funext fun i => by rw [lift_toPowerSeries, map_fst_lift]
    rw [hfam]

  set Φ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) 𝔻 :=
    fun i => subst (Sum.elim N F.toPowerSeries) ((L).toPowerSeries i) with hΦ
  have hΦ0 : ∀ j, (Φ j).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hN0 hF0
  have hΦred : ∀ j, MvPowerSeries.map φk (Φ j) = 0 := by
    intro j
    show MvPowerSeries.map φk (subst (Sum.elim N F.toPowerSeries) ((L).toPowerSeries j)) = 0
    rw [map_fst_subst_elim F₀ hN0 hF0 hNred hFred j]
    exact MvFormalGroup.subst_elim_negSeries_left F₀ F₀.constantCoeff_eq_zero j
  set Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun l => sndSeries (Φ l) with hΓdef
  have hΦΓ : Φ = fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l) :=
    funext fun l => eq_eps_smul_of_map_fst_eq_zero (hΦred l)
  have hΓ0 : ∀ l, (Γ l).constantCoeff = 0 := fun l => by
    have h := hΦ0 l
    rw [← coeff_zero_eq_constantCoeff_apply] at h ⊢
    show TrivSqZeroExt.snd (coeff 0 (Φ l)) = 0
    rw [h]
    rfl

  have hFT : F.toPowerSeries = tr F₀ Γ := by
    funext i
    rw [tr_apply, ← hΦΓ]
    show F.toPowerSeries i = subst (Sum.elim (L).toPowerSeries fun i =>
      subst (Sum.elim N F.toPowerSeries) ((L).toPowerSeries i)) ((L).toPowerSeries i)
    rw [← MvFormalGroup.subst_elim_assoc (L) (constantCoeff_L F₀) hN0 hF0 i]
    have hz : (fun j => subst (Sum.elim (L).toPowerSeries N) ((L).toPowerSeries j)) =
        fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) 𝔻) :=
      funext fun j => MvFormalGroup.subst_elim_negSeries (L) (constantCoeff_L F₀) j
    rw [hz, MvFormalGroup.subst_elim_zero_left (L) hF0 i]
  have hεΓ0 : ∀ l, ((ε : 𝔻) • MvPowerSeries.map ιk (Γ l)).constantCoeff = 0 :=
    fun l => constantCoeff_eps_smul_lift (hΓ0 l)

  have hswap0 : ∀ l, (subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
      fun j => X (Sum.inl j)) (Γ l)).constantCoeff = 0 := fun l =>
    constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim (fun j => constantCoeff_X _)
      fun j => constantCoeff_X _) (by rintro (j | j) <;> exact constantCoeff_X _) (hΓ0 l)
  have hsym : (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k)) fun j => X (Sum.inl j)) (Γ l))) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (Γ l) := by
    refine cancel_left (L) (constantCoeff_L F₀) (fun l => constantCoeff_eps_smul_lift (hswap0 l))
      hεΓ0 (funext fun i => ?_)
    have hc := MvFormalGroup.IsComm.comm (F := F) i
    rw [hFT, subst_tr F₀ hΓ0 (fun j => constantCoeff_X _) (fun j => constantCoeff_X _)
      (P₀ := fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) k))
      (Q₀ := fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ Fin n) k))
      (fun j => map_X _ _) (fun j => map_X _ _) i, tr_apply] at hc
    have hLc : (fun j => subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) 𝔻))
        fun j => X (Sum.inl j)) ((L).toPowerSeries j)) = (L).toPowerSeries :=
      funext fun j => MvFormalGroup.IsComm.comm (F := L) j
    rw [hLc] at hc
    exact hc

  have hA : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hA₀ : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB₀ : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC₀ : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun l => X (Sum.inr (Sum.inl l))) (F₀.toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim F₀ hA₀ hB₀
  have hFBC : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
      fun l => X (Sum.inr (Sum.inr l))) (F₀.toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim F₀ hB₀ hC₀
  have hu : ∀ l, (subst (Sum.elim (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inl l))) (F₀.toPowerSeries j))
        fun l => X (Sum.inr (Sum.inr l))) (Γ l) +
      subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inl l))) (Γ l)).constantCoeff = 0 := by
    intro l
    rw [map_add, constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hFAB hC₀)
      (by rintro (j | j); exacts [hFAB j, constantCoeff_X _]) (hΓ0 l),
      constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hA₀ hB₀)
      (by rintro (j | j) <;> exact constantCoeff_X _) (hΓ0 l), add_zero]
  have hv : ∀ l, (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
          fun l => X (Sum.inr (Sum.inr l))) (F₀.toPowerSeries j)) (Γ l) +
      subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inr l))) (Γ l)).constantCoeff = 0 := by
    intro l
    rw [map_add, constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hA₀ hFBC)
      (by rintro (j | j); exacts [constantCoeff_X _, hFBC j]) (hΓ0 l),
      constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim hB₀ hC₀)
      (by rintro (j | j) <;> exact constantCoeff_X _) (hΓ0 l), add_zero]
  have hLBC : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
      fun l => X (Sum.inr (Sum.inr l))) ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hB hC
  have hW : ∀ j, (subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
      fun j' => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
        fun l => X (Sum.inr (Sum.inr l))) ((L).toPowerSeries j')) ((L).toPowerSeries j)).constantCoeff = 0 :=
    MvFormalGroup.constantCoeff_subst_elim (L) hA hLBC
  have hcoc : (fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inl l))) (F₀.toPowerSeries j))
        fun l => X (Sum.inr (Sum.inr l))) (Γ l) +
      subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inl l))) (Γ l))) =
      fun l => (ε : 𝔻) • MvPowerSeries.map ιk (subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
          fun l => X (Sum.inr (Sum.inr l))) (F₀.toPowerSeries j)) (Γ l) +
      subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k))
        fun l => X (Sum.inr (Sum.inr l))) (Γ l)) := by
    refine cancel_left (L) hW (fun l => constantCoeff_eps_smul_lift (hu l))
      (fun l => constantCoeff_eps_smul_lift (hv l)) (funext fun i => ?_)
    have ha := F.assoc i
    rw [hFT, assoc_lhs hΓ0 i, assoc_rhs hΓ0 i] at ha
    have h3 : (fun j => subst (Sum.elim (fun j' => subst (Sum.elim
        (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
        fun l : Fin n => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
        ((L).toPowerSeries j'))
        fun l : Fin n => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
        ((L).toPowerSeries j)) =
        fun j => subst (Sum.elim (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
          fun j' => subst (Sum.elim
            (fun l : Fin n => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
            fun l : Fin n => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) 𝔻))
            ((L).toPowerSeries j')) ((L).toPowerSeries j) :=
      funext fun j => MvFormalGroup.subst_elim_assoc (L) hA hB hC j
    rw [h3] at ha
    exact ha
  refine ⟨Γ, fun l => ⟨hΓ0 l, ?_, ?_⟩, hFT⟩
  · exact eps_smul_lift_injective (congrFun hsym l)
  · exact eps_smul_lift_injective (congrFun hcoc l)

end Law

end Dual

end P2mFGTranslate
p2m_reactivate "P2MW.S_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq.P2mFGTranslate"

universe u

open P2mFGTranslate in
theorem solution
    {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm] :
    (∀ Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k, (∀ l, F₀.IsSymmTwoCocycle (Γ l)) →
      ∃ D : MvFormalGroup n (DualNumber k), D.IsComm ∧
        D.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ ∧
        ∀ i, D.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) ∧
    ∀ (F : MvFormalGroup n (DualNumber k)) [F.IsComm],
      F.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ →
      ∃ Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k, (∀ l, F₀.IsSymmTwoCocycle (Γ l)) ∧
        ∀ i, F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i)) := by
  refine ⟨fun Γ hΓ => ⟨defoLaw F₀ Γ hΓ, isComm_defoLaw hΓ, map_fst_defoLaw hΓ, fun i => ?_⟩, ?_⟩
  · show tr F₀ Γ i = _
    rw [tr_apply, map_toPowerSeries_fun]
  intro F _ hF
  obtain ⟨Γ, hΓ, hFT⟩ := exists_isSymmTwoCocycle_of_map_fst_eq (F₀ := F₀) F hF
  refine ⟨Γ, hΓ, fun i => ?_⟩
  rw [hFT, tr_apply, map_toPowerSeries_fun]

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq.P2mFGTranslate"

end S_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
end P2MW
export P2MW.S_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq (solution)
